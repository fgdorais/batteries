/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis, Gabriel Ebner
-/

import Std.Util.TermUnsafe
import Std.Lean.NameMapAttribute
open Lean Meta

namespace Std.Tactic.Lint

/-!
# Basic linter types and attributes

This file defines the basic types and attributes used by the linting
framework.  A linter essentially consists of a function
`(declaration : Name) → MetaM (Option MessageData)`, this function together with some
metadata is stored in the `Linter` structure. We define two attributes:

 * `@[stdLinter]` applies to a declaration of type `Linter` and adds it to the default linter set.

 * `@[nolint linterName]` omits the tagged declaration from being checked by
   the linter with name `linterName`.
-/

/-- `@[nolint linterName]` omits the tagged declaration from being checked by
the linter with name `linterName`. -/
syntax (name := nolint) "nolint" (ppSpace ident)+ : attr

/-- Defines the user attribute `nolint` for skipping `#lint` -/
initialize nolintAttr : NameMapExtension (Array Name) ←
  registerNameMapAttribute {
    name := `nolint
    descr := "Do not report this declaration in any of the tests of `#lint`"
    add := fun _decl stx =>
      match stx with
        -- TODO: validate linter names
        | `(attr|nolint $[$ids]*) => pure $ ids.map (·.getId.eraseMacroScopes)
        | _ => throwError "unexpected nolint syntax {stx}"
  }

/-- Returns true if `decl` should be checked
using `linter`, i.e., if there is no `nolint` attribute. -/
def shouldBeLinted [Monad m] [MonadEnv m] (linter : Name) (decl : Name) : m Bool :=
  return !((nolintAttr.find? (← getEnv) decl).getD {}).contains linter

/--
Returns true if `decl` is an automatically generated declaration.

Also returns true if `decl` is an internal name or created during macro
expansion.
-/
def isAutoDecl (decl : Name) : CoreM Bool := do
  if decl.hasMacroScopes then return true
  if decl.isInternal then return true
  if let Name.str n s := decl then
    if s.startsWith "proof_" || s.startsWith "match_" then return true
    if (← getEnv).isConstructor n && ["injEq", "inj", "sizeOf_spec"].any (· == s) then
      return true
    if let ConstantInfo.inductInfo _ := (← getEnv).find? n then
      if [casesOnSuffix, recOnSuffix, brecOnSuffix, binductionOnSuffix, belowSuffix, "ibelow",
          "ndrec", "ndrecOn", "noConfusionType", "noConfusion", "ofNat", "toCtorIdx"
        ].any (· == s) then
        return true
      if let some _ := isSubobjectField? (← getEnv) n s then
        return true
  pure false

/-- A linting test for the `#lint` command. -/
structure Linter where
  /-- `test` defines a test to perform on every declaration. It should never fail. Returning `none`
  signifies a passing test. Returning `some msg` reports a failing test with error `msg`. -/
  test : Name → MetaM (Option MessageData)
  /-- `noErrorsFound` is the message printed when all tests are negative -/
  noErrorsFound : MessageData
  /-- `errorsFound` is printed when at least one test is positive -/
  errorsFound : MessageData
  /-- If `isFast` is false, this test will be omitted from `#lint-`. -/
  isFast := true

/-- A `NamedLinter` is a linter associated to a particular declaration. -/
structure NamedLinter extends Linter where
  /-- The linter declaration name -/
  declName : Name

/-- The name of the named linter. This is just the declaration name without the namespace. -/
def NamedLinter.name (l : NamedLinter) : Name := l.declName.updatePrefix Name.anonymous

/-- Gets a linter by declaration name. -/
def getLinter (declName : Name) : CoreM NamedLinter := unsafe
  return { ← evalConstCheck Linter ``Linter declName with declName }

/-- Takes a list of names that resolve to declarations of type `linter`,
and produces a list of linters. -/
def getLinters (l : List Name) : CoreM (List NamedLinter) :=
  l.mapM getLinter

/-- Defines the user attribute `stdLinter` for adding a linter to the default set. -/
initialize stdLinterAttr : TagAttribute ←
  registerTagAttribute
    (name := `stdLinter)
    (descr := "Use this declaration as a linting test in #lint")
    (validate := fun name => do
      let constInfo ← getConstInfo name
      unless ← (isDefEq constInfo.type (mkConst ``Linter)).run' do
        throwError "must have type Linter, got {constInfo.type}")