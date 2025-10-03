import Strata.DL.Imperative.CmdSemantics
import Plausible.DeriveArbitrary
import Plausible.Attr
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.DeriveChecker

open Imperative Plausible

def foo : 1 + 1 = 2 := by decide

inductive Tree (α : Type) : Type where
| Leaf : Tree α
| Node : α → Tree α → Tree α → Tree α
deriving BEq, Repr

set_option trace.plausible.deriving.arbitrary true in
deriving instance Arbitrary for Tree

-- why?
/-- error: Failed to delta derive instance, `Tree` is not a definition.
-/
#guard_msgs in
deriving instance Arbitrary for (Tree Nat)

#eval @Arbitrary.runArbitrary Nat _ 42

#eval @Arbitrary.runArbitrary (Tree Nat) _ 3

#print optParam

#print PureExpr

inductive ArithExpr where
| const : Int → ArithExpr
| var   : String → ArithExpr
| add   : ArithExpr → ArithExpr → ArithExpr
| lNeg   : ArithExpr → ArithExpr -- logical negation: neg 0 = 1, neg (non-zero) = 0
deriving Repr, BEq, DecidableEq

set_option trace.plausible.deriving.arbitrary true in
deriving instance Arbitrary for ArithExpr

abbrev Arith : PureExpr where
  Ident := String
  Expr  := ArithExpr
  Ty    := Unit
  TyEnv := String → Unit
  EvalEnv := String → Int
  EqIdent := by infer_instance

class Pointed

-- instance : Arbitrary

/-
inductive Imperative.Cmd : PureExpr → Type
number of parameters: 1
constructors:
Imperative.Cmd.init : {P : PureExpr} → P.Ident → P.Ty → P.Expr → optParam (MetaData P) MetaData.empty → Cmd P
Imperative.Cmd.set : {P : PureExpr} → P.Ident → P.Expr → optParam (MetaData P) MetaData.empty → Cmd P
Imperative.Cmd.havoc : {P : PureExpr} → P.Ident → optParam (MetaData P) MetaData.empty → Cmd P
Imperative.Cmd.assert : {P : PureExpr} → String → P.Expr → optParam (MetaData P) MetaData.empty → Cmd P
Imperative.Cmd.assume : {P : PureExpr} → String → P.Expr → optParam (MetaData P) MetaData.empty → Cmd P
-/
#print Imperative.Cmd

-- set_option diagnostics true

inductive ArithCmd where
| init : Arith.Ident → Arith.Ty → Arith.Expr → optParam (MetaData Arith) MetaData.empty → ArithCmd
| set : Arith.Ident → Arith.Expr → optParam (MetaData Arith) MetaData.empty → ArithCmd
| havoc : Arith.Ident → optParam (MetaData Arith) MetaData.empty → ArithCmd
| assert : String → Arith.Expr → optParam (MetaData Arith) MetaData.empty → ArithCmd
| assume : String → Arith.Expr → optParam (MetaData Arith) MetaData.empty → ArithCmd

instance : Repr ArithCmd where
  reprPrec
    | ArithCmd.init id ty e _md, _ => "(init " ++ repr id ++ " " ++ repr ty ++ " " ++ repr e ++ ")"
    | ArithCmd.set id e _md, _ => "(set " ++ repr id ++ " " ++ repr e ++ ")"
    | ArithCmd.havoc id _md, _ => "(havoc " ++ repr id ++ ")"
    | ArithCmd.assert msg e _md, _ => "(assert " ++ repr msg ++ " " ++ repr e ++ ")"
    | ArithCmd.assume msg e _md, _ => "(assume " ++ repr msg ++ " " ++ repr e ++ ")"


instance : Arbitrary (optParam α a) where
  arbitrary := return a

instance : Arbitrary (MetaData Arith) where
  arbitrary := return MetaData.empty

-- set_option trace.plausible.deriving.arbitrary true in
deriving instance Arbitrary for ArithCmd

#eval Gen.run (Arbitrary.arbitrary : Gen ArithExpr) 4

#eval Gen.printSamples (Arbitrary.arbitrary : Gen ArithCmd)

instance : HasFvar Arith where
  mkFvar id := ArithExpr.var id
  getFvar e := match e with
    | ArithExpr.var id => some id
    | _ => none

instance : HasBool Arith where
  tt := ArithExpr.const 1
  ff := ArithExpr.const 0

instance : HasBoolNeg Arith where
  neg e := ArithExpr.lNeg e

-- doesn't work atm
-- set_option trace.plausible.deriving.arbitrary true in
-- deriving instance Arbitrary for Imperative.Cmd


-- Need to introduce this
inductive SemanticStoreArith where | mk (f : Arith.Ident → Option Arith.Expr) : SemanticStoreArith

def SemanticStoreArith.get (σ : SemanticStoreArith) := match σ with | .mk f => f

-- Need to introduce this!
def agreesOnExcept (σ σ' : SemanticStoreArith) (x : String) : Prop :=
  ∀ y, x ≠ y → σ.get y = σ'.get y

inductive InitStateArith : SemanticStoreArith → Arith.Ident → Arith.Expr → SemanticStoreArith → Prop where
  | init :
    σ.get x = none →
    σ'.get x = .some v →
    agreesOnExcept σ σ' x →
    ----
    InitStateArith σ x v σ'

def update (σ : SemanticStoreArith) (x : Arith.Ident) (v : Arith.Expr) : SemanticStoreArith :=
  ⟨fun y => if x = y then .some v else σ.get y⟩

inductive UpdateStateArith : SemanticStoreArith → Arith.Ident → Arith.Expr → SemanticStoreArith → Prop where
  | update :
    σ.get x = .some v' →
    σ'.get x = .some v →
    agreesOnExcept σ σ' x →
    ----
    UpdateStateArith σ x v σ'

def testStore : SemanticStoreArith :=
  ⟨fun
  | "x" => .some (ArithExpr.const 1)
  | "y" => .some (ArithExpr.const 2)
  | _   => none⟩

#check repr

#print Std.Format

instance : Repr (SemanticStoreArith) where
  reprPrec σ _ := "{ " ++ Std.Format.joinSep (List.map (fun id => id ++ " ↦ " ++ repr (σ.get id)) ["x", "y", "z"]) ", " ++ " }"

#eval testStore

#check ArbitrarySuchThat

instance instStoreUpdate (σ : SemanticStoreArith) (x : Arith.Ident) :
  ArbitrarySuchThat SemanticStoreArith (fun σ' => agreesOnExcept σ σ' x) where
  arbitraryST := do
    let v ← Arbitrary.arbitrary
    return update σ x v

instance instStoreUpdate' (σ : SemanticStoreArith) (x : Arith.Ident) :
  ArbitrarySizedSuchThat SemanticStoreArith (fun σ' => agreesOnExcept σ σ' x) where
  arbitrarySizedST _ := do
    let v ← Arbitrary.arbitrary
    return update σ x v


#check (fun n : Nat => ∃ m, n < m)

instance : DecidableEq String := by infer_instance
instance : Repr String := by infer_instance

#check (· < ·)

instance [Decidable P] : DecOpt P := by infer_instance

instance : DecidableEq Arith.Expr := by infer_instance

-- Notes
-- First of all, we had to hide the domain constraint
-- into `agreesOnExcept`. Error messages was mysterious
-- ("Cannot convert expression {e} to Range")
-- Second error:
-- DFS: unable to convert Expr String → Option Arith.Expr to a HypothesisExpr
-- ?
set_option trace.plausible.deriving.arbitrary true in
#derive_generator (fun (σ : SemanticStoreArith) => InitStateArith testStore "x" (.const 2) σ)

instance : ArbitrarySizedSuchThat SemanticStoreArith (fun σ_1 => InitStateArith testStore_1 _1 _2 σ_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (testStore_1 : SemanticStoreArith) (_1 : Arith.Ident)
      (_2 : Arith.Expr) : Plausible.Gen SemanticStoreArith :=
      match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1,
              match DecOpt.decOpt (Eq (SemanticStoreArith.get testStore_1 _1) (Option.none)) initSize with
              | Except.ok Bool.true => do
                let σ_1 ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun σ_1 => agreesOnExcept testStore_1 σ_1 _1) initSize;
                match DecOpt.decOpt (Eq (SemanticStoreArith.get σ_1 _1) (Option.some _2)) initSize with
                  | Except.ok Bool.true => return σ_1
                  | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
          [(1,
              match DecOpt.decOpt (Eq (SemanticStoreArith.get testStore_1 _1) (Option.none)) initSize with
              | Except.ok Bool.true => do
                let σ_1 ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun σ_1 => agreesOnExcept testStore_1 σ_1 _1) initSize;
                match DecOpt.decOpt (Eq (SemanticStoreArith.get σ_1 _1) (Option.some _2)) initSize with
                  | Except.ok Bool.true => return σ_1
                  | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            ]
    fun size => aux_arb size size testStore_1 _1 _2

def arithEval (σ_old : SemanticStoreArith) (σ : SemanticStoreArith) : Arith.Expr → Option Arith.Expr
| .const n => pure <| .const n
| .var s => σ.get s
| .add e1 e2 => do
  let .const n1 ← arithEval σ_old σ e1 | failure
  let .const n2 ← arithEval σ_old σ e2 | failure
  pure <| .const (n1 + n2)
| .lNeg e => do
  let v ← arithEval σ_old σ e
  match v with
  | .const 0 => pure <| .const 1
  | .const _ => pure <| .const 0
  | _ => failure


/--
An inductively-defined operational semantics that depends on
environment lookup and evaluation functions for expressions.
-/
inductive EvalArithCmd : SemanticStoreArith → SemanticStoreArith → ArithCmd → SemanticStoreArith → Prop where
  | eval_init :
    arithEval σ₀ σ e = .some v →
    InitStateArith σ x v σ' →
    ---
    EvalArithCmd σ₀ σ (.init x _ e _) σ'

  | eval_set :
    arithEval σ₀ σ e = .some v →
    UpdateStateArith σ x v σ' →
    ----
    EvalArithCmd σ₀ σ (.set x e _) σ'

  | eval_havoc :
    UpdateStateArith σ x v σ' →
    ----
    EvalArithCmd σ₀ σ (.havoc x _) σ'

  | eval_assert :
    arithEval σ₀ σ e = .some HasBool.tt →
    ----
    EvalArithCmd σ₀ σ (.assert _ e _) σ

  | eval_assume :
    arithEval σ₀ σ e = .some HasBool.tt →
    ----
    EvalArithCmd σ₀ σ (.assume _ e _) σ
