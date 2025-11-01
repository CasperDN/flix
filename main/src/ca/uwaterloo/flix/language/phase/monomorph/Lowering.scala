/*
 * Copyright 2021 Magnus Madsen
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package ca.uwaterloo.flix.language.phase.monomorph

import ca.uwaterloo.flix.api.Flix
import ca.uwaterloo.flix.language.ast.LoweredAst.{Expr, Instance}
import ca.uwaterloo.flix.language.ast.Type.eraseAliases
import ca.uwaterloo.flix.language.ast.ops.TypedAstOps
import ca.uwaterloo.flix.language.ast.shared.*
import ca.uwaterloo.flix.language.ast.shared.SymUse.*
import ca.uwaterloo.flix.language.ast.{AtomicOp, Kind, LoweredAst, MonoAst, Name, Scheme, SourceLocation, Symbol, Type, TypeConstructor, TypedAst}
import ca.uwaterloo.flix.language.dbg.AstPrinter.DebugLoweredAst
import ca.uwaterloo.flix.language.phase.monomorph.Specialization.{Context, StrictSubstitution}
import ca.uwaterloo.flix.util.collection.{ListOps, Nel}
import ca.uwaterloo.flix.util.{InternalCompilerException, ParOps}

/**
  * This phase translates AST expressions related to the Datalog subset of the
  * language into `Fixpoint.Ast.Datalog` values (which are ordinary Flix values).
  * This allows the Datalog engine to be implemented as an ordinary Flix program.
  *
  * In addition to translating expressions, types must also be translated from
  * Schema types to enum types.
  *
  * Finally, values must be boxed using the Boxable.
  */

// TODO: Long-term improvements:
// - Return a [[Validation]] from visitExp etc.
// - Decide which expressions to allow as head and body terms.

object Lowering {
  private object Defs {

    lazy val ChannelNewTuple: Symbol.DefnSym = Symbol.mkDefnSym("Concurrent.Channel.newChannelTuple")

  }

  private object Enums {

    lazy val ChannelMpmc: Symbol.EnumSym = Symbol.mkEnumSym("Concurrent.Channel.Mpmc")
  }

  private object Types {
    //
    // Data Types
    //
    lazy val ChannelMpmc: Type = Type.Cst(TypeConstructor.Enum(Enums.ChannelMpmc, Kind.Star ->: Kind.Eff ->: Kind.Star), SourceLocation.Unknown)


  }

  /**
    * Returns the definition associated with the given symbol `sym`.
    *
    * @param tpe must be subst. Can be visited, if the underlying function can handle that
    */
  private def lookup(sym: Symbol.DefnSym, tpe: Type)(implicit ctx: Context, root: LoweredAst.Root, flix: Flix): Symbol.DefnSym =
    Specialization.specializeDefnSym(sym, tpe)


  def visitNewChannel(exp: LoweredAst.Expr, tpe: Type, eff: Type, loc: SourceLocation, env0: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)(implicit ctx: Context, instances: Map[(Symbol.TraitSym, TypeConstructor), Instance], root: LoweredAst.Root, flix: Flix): MonoAst.Expr = {
    val e = Specialization.specializeExp(exp, env0, subst)
    mkNewChannelTuple(e, tpe, eff, loc)
  }

  /**
    * Lowers the given type `tpe0` which must not be a schema type.
    *
    * Performance Note: We are on a hot path. We take extra care to avoid redundant type objects.
    */
  private def visitType(tpe0: Type)(implicit root: LoweredAst.Root, flix: Flix): Type = tpe0 match {
    case Type.Cst(_, _) => tpe0 // Performance: Reuse tpe0.

    case Type.Var(_, _) => tpe0

    // Rewrite Sender[t] to Concurrent.Channel.Mpmc[t, IO]
    case Type.Apply(Type.Cst(TypeConstructor.Sender, loc), tpe, _) =>
      val t = visitType(tpe)
      mkChannelTpe(t, loc)

    // Rewrite Receiver[t] to Concurrent.Channel.Mpmc[t, IO]
    case Type.Apply(Type.Cst(TypeConstructor.Receiver, loc), tpe, _) =>
      val t = visitType(tpe)
      mkChannelTpe(t, loc)

    case Type.Apply(tpe1, tpe2, loc) =>
      val t1 = visitType(tpe1)
      val t2 = visitType(tpe2)
      // Performance: Reuse tpe0, if possible.
      if ((t1 eq tpe1) && (t2 eq tpe2)) {
        tpe0
      } else {
        Type.Apply(t1, t2, loc)
      }

    case Type.Alias(sym, args, t, loc) =>
      Type.Alias(sym, args.map(visitType), visitType(t), loc)

    case Type.AssocType(cst, args, kind, loc) =>
      Type.AssocType(cst, args.map(visitType), kind, loc) // TODO ASSOC-TYPES can't put lowered stuff on right side of assoc type def...

    case Type.JvmToType(_, loc) => throw InternalCompilerException("unexpected JVM type", loc)

    case Type.JvmToEff(_, loc) => throw InternalCompilerException("unexpected JVM eff", loc)

    case Type.UnresolvedJvmType(_, loc) => throw InternalCompilerException("unexpected JVM type", loc)
  }

  /**
    * Make a new channel tuple (sender, receiver) expression
    */
  private def mkNewChannelTuple(exp: MonoAst.Expr, tpe: Type, eff: Type, loc: SourceLocation)(implicit ctx: Context, root: LoweredAst.Root, flix: Flix): MonoAst.Expr = {
    val itpe = Type.mkIoArrow(exp.tpe, tpe, loc)
    val defnSym = lookup(Defs.ChannelNewTuple, itpe)
    MonoAst.Expr.ApplyDef(defnSym, exp :: Nil, visitType(itpe), visitType(tpe), eff, loc)
  }

  /**
    * The type of a channel which can transmit variables of type `tpe`.
    */
  private def mkChannelTpe(tpe: Type, loc: SourceLocation): Type = {
    mkChannelTpe(tpe, Type.IO, loc)
  }

  /**
    * The type of a channel which can transmit variables of type `tpe1` in region `tpe2`.
    */
  private def mkChannelTpe(tpe1: Type, tpe2: Type, loc: SourceLocation): Type = {
    Type.Apply(Type.Apply(Types.ChannelMpmc, tpe1, loc), tpe2, loc)
  }

  /**
    * Returns a desugared let-match expression, i.e.
    * {{{
    *   let pattern = exp;
    *   body
    * }}}
    * is desugared to
    * {{{
    *   match exp {
    *     case pattern => body
    *   }
    * }}}
    */

}
