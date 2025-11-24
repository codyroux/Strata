import Strata.DL.Imperative.CmdSemantics
import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.LExprTypeSpec
import Strata.DL.Lambda.LExprTypeEnv
import Strata.DL.Lambda.LExprWF
import Strata.DL.Lambda.LExprT
import Strata.DL.Lambda.LExprEval
import Strata.DL.Lambda.IntBoolFactory
import Plausible.Sampleable
import Plausible.DeriveArbitrary
import Plausible.Attr
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.DeriveChecker

open Imperative Plausible

inductive ArithExpr where
| const : Int → ArithExpr
| var   : String → ArithExpr
| add   : ArithExpr → ArithExpr → ArithExpr
| lNeg   : ArithExpr → ArithExpr -- logical negation: neg 0 = 1, neg (non-zero) = 0
deriving Repr, BEq, DecidableEq

set_option trace.plausible.deriving.arbitrary true in
deriving instance Arbitrary for ArithExpr

#print PureExpr

abbrev Arith : PureExpr where
  Ident := String
  Expr  := ArithExpr
  Ty    := Unit
  TyContext := Unit
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


instance : HasFvar Arith where
  mkFvar id := ArithExpr.var id
  getFvar e := match e with
    | ArithExpr.var id => some id
    | _ => none

instance : HasBool Arith where
  tt := ArithExpr.const 1
  ff := ArithExpr.const 0

instance [Decidable P] : DecOpt P := by infer_instance

instance : DecidableEq Arith.Expr := by infer_instance

#print Lambda.LExpr
#print Lambda.Info
#print Lambda.QuantifierKind

deriving instance Arbitrary for Lambda.Identifier
deriving instance Arbitrary for Lambda.Info
deriving instance Arbitrary for Lambda.QuantifierKind

#print Gen.chooseNat

instance instArbitraryRat : Arbitrary Rat where
  arbitrary := do
  let den ← Gen.chooseNat
  let num : Int ← Arbitrary.arbitrary
  return num / den

deriving instance Arbitrary for Lambda.LConst

deriving instance Arbitrary for Lambda.LExpr

#eval Gen.printSamples (Arbitrary.arbitrary : Gen <| Lambda.LExpr String String)

#print Lambda.TContext
#print Lambda.LContext

#print Lambda.LExpr.HasType

#print DecidableEq

-- derive_generator (fun idMeta inst env ctx ty => ∃ t, @Lambda.LExpr.HasType idMeta inst env ctx t ty)

open Lambda
open LTy

/--
Close `ty` by `x`, i.e., add `x` as a bound type variable.
-/
def LTy.close (x : TyIdentifier) (ty : LTy) : LTy :=
  match ty with
  | .forAll vars lty => .forAll (x :: vars) lty

/--
Open `ty` by instantiating the bound type variable `x` with `xty`.
-/
def LTy.open (x : TyIdentifier) (xty : LMonoTy) (ty : LTy) : LTy :=
  match ty with
  | .forAll vars lty =>
    if x ∈ vars then
      let S := [(x, xty)]
      .forAll (vars.removeAll [x]) (LMonoTy.subst [S] lty)
    else
      ty

def varClose (k : Nat) (x : Identifier Unit) (e : LExpr LMonoTy Unit) : LExpr LMonoTy Unit :=
  match e with
  | .const c => .const c
  | .op o ty => .op o ty
  | .bvar i => .bvar i
  | .fvar y _ => if (x == y) then
                      (.bvar k) else e
  | .mdata info e' => .mdata info (varClose k x e')
  | .abs ty e' => .abs ty (varClose (k + 1) x e')
  | .quant qk ty tr' e' => .quant qk ty (varClose (k + 1) x tr') (varClose (k + 1) x e')
  | .app e1 e2 => .app (varClose k x e1) (varClose k x e2)
  | .ite c t e => .ite (varClose k x c) (varClose k x t) (varClose k x e)
  | .eq e1 e2 => .eq (varClose k x e1) (varClose k x e2)

inductive MapFind : Map α β → α → β → Prop where
| hd : MapFind ((x, y) :: m) x y
| tl : MapFind m x y → MapFind (p :: m) x y

inductive MapsFind : Maps α β → α → β → Prop where
| hd : MapFind m x y → MapsFind (m :: ms) x y
| tl : MapsFind ms x y → MapsFind (m :: ms) x y

inductive MapFind₂ {α β : Type} : Map α β → α × β → Prop where
| hd : MapFind₂ ((x, y) :: m) (x, y)
| tl : MapFind₂ m q → MapFind₂ (p :: m) q

inductive MapsFind₂ : Maps α β → α × β → Prop where
| hd : MapFind₂ m (x, y) → MapsFind₂ (m :: ms) (x, y)
| tl : MapsFind₂ ms (x, y) → MapsFind₂ (m :: ms) (x, y)


inductive MapReplace : Map α β → α → β → Map α β → Prop where
| nil : MapReplace [] x y []
| consFound : MapReplace ((x, z)::m) x y ((x, y)::m)
| consNotFound : x ≠ z → MapReplace m x y m' → MapReplace ((z, w) :: m) x y ((z, w) :: m')


inductive MapsReplace : Maps α β → α → β → Maps α β → Prop where
| nil : MapsReplace [] x y []
-- We do redundant work here but it's ok
| cons : MapReplace m x y m' → MapsReplace ms x y ms' → MapsReplace (m::ms) x y (m'::ms')

inductive MapNotFound : Map α β → α → Prop where
| nil : MapNotFound [] x
| cons : x ≠ z → MapNotFound m x → MapNotFound ((z, w) :: m) x

inductive MapsNotFound : Maps α β → α → Prop where
| nil : MapsNotFound [] x
| cons : MapNotFound m x → MapsNotFound ms x → MapsNotFound (m::ms) x

-- We tediously do what the functional implementation does but allowing shadowing would probably be ok
inductive MapsInsert : Maps α β → α → β → Maps α β → Prop where
| found : MapsFind ms x z → MapsReplace ms x y ms' → MapsInsert ms x y ms'
| notFound : MapsNotFound (m::ms) x → MapsInsert (m::ms) x y (((x,y)::m)::ms)
| empty : MapsInsert [] x y [[(x, y)]]


instance instStringSuchThatIsInt : ArbitrarySizedSuchThat String (fun s => s.isInt) where
  arbitrarySizedST _ := toString <$> (Arbitrary.arbitrary : Gen Int)

#eval
  let P : String → Prop := fun s => s.isInt
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

def ArrayFind (a : Array α) (x : α)  := x ∈ a

instance instArrayFindSuchThat {α} {a} : ArbitrarySizedSuchThat α (fun x => ArrayFind a x) where
  arbitrarySizedST _ := do
  if h:a.size = 0 then throw <| GenError.genError "Gen: cannot generate elements of empty array" else
  let i ← Gen.chooseNatLt 0 a.size (by omega)
  return a[i.val]

/-
inductive HasType {IDMeta : Type} [DecidableEq IDMeta] (C: LContext IDMeta):
  (TContext IDMeta) → (LExpr LMonoTy IDMeta) → LTy → Prop where
  | tmdata : ∀ Γ info e ty, HasType C Γ e ty →
                            HasType C Γ (.mdata info e) ty

  | tbool_const : ∀ Γ b,
            C.knownTypes.containsName "bool" →
            HasType C Γ (.boolConst b) (.forAll [] .bool)
  | tint_const : ∀ Γ n,
            C.knownTypes.containsName "int" →
            HasType C Γ (.intConst n) (.forAll [] .int)
  | treal_const : ∀ Γ r,
            C.knownTypes.containsName "real" →
            HasType C Γ (.realConst r) (.forAll [] .real)
  | tstr_const : ∀ Γ s,
            C.knownTypes.containsName "string" →
            HasType C Γ (.strConst s) (.forAll [] .string)
  | tbitvec_const : ∀ Γ n b,
            C.knownTypes.containsName "bitvec" →
            HasType C Γ (.bitvecConst n b) (.forAll [] (.bitvec n))

  | tvar : ∀ Γ x ty, Γ.types.find? x = some ty → HasType C Γ (.fvar x none) ty

  /-
  For an annotated free variable (or operator, see `top_annotated`), it must be
  the case that the claimed type `ty_s` is an instantiation of the general type
  `ty_o`. It suffices to show the existence of a list `tys` that, when
  substituted for the bound variables in `ty_o`, results in `ty_s`.
  -/
  | tvar_annotated : ∀ Γ x ty_o ty_s tys,
            Γ.types.find? x = some ty_o →
            tys.length = ty_o.boundVars.length →
            LTy.openFull ty_o tys = ty_s →
            HasType C Γ (.fvar x (some ty_s)) (.forAll [] ty_s)

  | tabs : ∀ Γ x x_ty e e_ty o,
            LExpr.fresh x e →
            (hx : LTy.isMonoType x_ty) →
            (he : LTy.isMonoType e_ty) →
            HasType C { Γ with types := Γ.types.insert x.fst x_ty} (LExpr.varOpen 0 x e) e_ty →
            o = none ∨ o = some (x_ty.toMonoType hx) →
            HasType C Γ (.abs o e)
                      (.forAll [] (.tcons "arrow" [(LTy.toMonoType x_ty hx),
                                                   (LTy.toMonoType e_ty he)]))

  | tapp : ∀ Γ e1 e2 t1 t2,
            (h1 : LTy.isMonoType t1) →
            (h2 : LTy.isMonoType t2) →
            HasType C Γ e1 (.forAll [] (.tcons "arrow" [(LTy.toMonoType t2 h2),
                                                     (LTy.toMonoType t1 h1)])) →
            HasType C Γ e2 t2 →
            HasType C Γ (.app e1 e2) t1

  -- `ty` is more general than `e_ty`, so we can instantiate `ty` with `e_ty`.
  | tinst : ∀ Γ e ty e_ty x x_ty,
            HasType C Γ e ty →
            e_ty = LTy.open x x_ty ty →
            HasType C Γ e e_ty

  -- The generalization rule will let us do things like the following:
  -- `(·ftvar "a") → (.ftvar "a")` (or `a → a`) will be generalized to
  -- `(.btvar 0) → (.btvar 0)` (or `∀a. a → a`), assuming `a` is not in the
  -- context.
  | tgen : ∀ Γ e a ty,
            HasType C Γ e ty →
            TContext.isFresh a Γ →
            HasType C Γ e (LTy.close a ty)

  | tif : ∀ Γ c e1 e2 ty,
            HasType C Γ c (.forAll [] .bool) →
            HasType C Γ e1 ty →
            HasType C Γ e2 ty →
            HasType C Γ (.ite c e1 e2) ty

  | teq : ∀ Γ e1 e2 ty,
            HasType C Γ e1 ty →
            HasType C Γ e2 ty →
            HasType C Γ (.eq e1 e2) (.forAll [] .bool)

  | tquant: ∀ Γ k tr tr_ty x x_ty e o,
            LExpr.fresh x e →
            (hx : LTy.isMonoType x_ty) →
            HasType C { Γ with types := Γ.types.insert x.fst x_ty} (LExpr.varOpen 0 x e) (.forAll [] .bool) →
            HasType C {Γ with types := Γ.types.insert x.fst x_ty} (LExpr.varOpen 0 x tr) tr_ty →
            o = none ∨ o = some (x_ty.toMonoType hx) →
            HasType C Γ (.quant k o tr e) (.forAll [] .bool)
  | top: ∀ Γ f op ty,
            C.functions.find? (fun fn => fn.name == op) = some f →
            f.type = .ok ty →
            HasType C Γ (.op op none) ty
  /-
  See comments in `tvar_annotated`.
  -/
  | top_annotated: ∀ Γ f op ty_o ty_s tys,
            C.functions.find? (fun fn => fn.name == op) = some f →
            f.type = .ok ty_o →
            tys.length = ty_o.boundVars.length →
            LTy.openFull ty_o tys = ty_s →
            HasType C Γ (.op op (some ty_s)) (.forAll [] ty_s)


-/

-- We massage the `HasType` definition to be more amenable to generation
inductive HasType : (LContext Unit) → (TContext Unit) → (LExpr LMonoTy Unit) → LTy → Prop where

  | tbool_const : ∀ C Γ b,
            HasType C Γ (.boolConst b) (.forAll [] .bool)
  | tint_const : ∀ C Γ n,
            HasType C Γ (.intConst n) (.forAll [] .int)
  | treal_const : ∀ C Γ r,
            HasType C Γ (.realConst r) (.forAll [] .real)
  | tstr_const : ∀ C Γ s,
            HasType C Γ (.strConst s) (.forAll [] .string)
  | tbitvec_const : ∀ C Γ n b,
            HasType C Γ (.bitvecConst n b) (.forAll [] (.bitvec n))

  | tvar : ∀ C Γ x ty, MapsFind Γ.types x ty → HasType C Γ (.fvar x none) ty

  | tabs : ∀ C Γ Γ' x x_ty e e_ty,
            MapsInsert Γ.types x (.forAll [] x_ty) Γ' →
            HasType C { Γ with types := Γ'} e (.forAll [] e_ty) →
            HasType C Γ (.abs .none <| varClose 0 x e)
                        (.forAll [] (.tcons "arrow" [x_ty, e_ty]))

  | tapp : ∀ C Γ e1 e2 t1 t2,
            (h1 : LTy.isMonoType t1) →
            (h2 : LTy.isMonoType t2) →
            HasType C Γ e1 (.forAll [] (.tcons "arrow" [(LTy.toMonoType t2 h2),
                                                        (LTy.toMonoType t1 h1)])) →
            HasType C Γ e2 t2 →
            HasType C Γ (.app e1 e2) t1

  | tif : ∀ C Γ c e1 e2 ty,
          HasType C Γ c (.forAll [] (.tcons "bool" [])) →
          HasType C Γ e1 ty →
          HasType C Γ e2 ty →
          HasType C Γ (.ite c e1 e2) ty

  | teq : ∀ C Γ e1 e2 ty,
          HasType C Γ e1 ty →
          HasType C Γ e2 ty →
          HasType C Γ (.eq e1 e2) (.forAll [] (.tcons "bool" []))

  | top: ∀ C Γ f ty,
            ArrayFind C.functions f →
            HasType C Γ (.op f.name none) ty

  -- -- We only generate monomorphic types for now
  -- -- `ty` is more general than `e_ty`, so we can instantiate `ty` with `e_ty`.
  -- | tinst : ∀ Γ e ty e_ty x x_ty,
  --           HasType C Γ e ty →
  --           e_ty = LTy.open x x_ty ty →
  --           HasType C Γ e e_ty

  -- -- The generalization rule will let us do things like the following:
  -- -- `(·ftvar "a") → (.ftvar "a")` (or `a → a`) will be generalized to
  -- -- `(.btvar 0) → (.btvar 0)` (or `∀a. a → a`), assuming `a` is not in the
  -- -- context.
  -- | tgen : ∀ Γ e a ty,
  --           HasType C Γ e ty →
  --           TContext.isFresh a Γ →
  --           HasType C Γ e (LTy.close a ty)

instance : Arbitrary TyIdentifier where
  arbitrary := Gen.oneOf #[return "A", return "B", return "C", return "D"]

#print LMonoTy

instance : Arbitrary LMonoTy where
  arbitrary :=
    let rec aux (n : Nat) : Gen LMonoTy :=
    match n with
    | 0 => Gen.oneOf #[return .tcons "int" [], return .tcons "bool" []]
    | n'+1 => do
    let choice ← Gen.chooseNatLt 0 3 (by simp)
    if ↑choice = 0 then
      Gen.oneOf #[return .tcons "int" [], return .tcons "bool" []]
    else if ↑choice = 1 then
        let ty1 ← aux n'
        let ty2 ← aux n'
        return .tcons "arrow" [ty1, ty2]
    else
      let n ← Gen.chooseNatLt 0 4 (by simp) -- Keep things bounded
      return .bitvec n
  do
    let ⟨size⟩ ← read
    aux size

instance : Arbitrary LTy where
  arbitrary := LTy.forAll [] <$> Arbitrary.arbitrary

-- #eval Gen.printSamples (Arbitrary.arbitrary : Gen LMonoTy)

instance {α β m_1 y_1_1} [BEq β] : ArbitrarySizedSuchThat α (fun x_1_1 => @MapFind α β m_1 x_1_1 y_1_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (α_1 : Type) (β_1 : Type) (m_1 : Map α β) (y_1_1 : β) :
      Plausible.Gen α :=
      (match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1,
              match m_1 with
              | List.cons (Prod.mk x y) m =>
                match DecOpt.decOpt (BEq.beq y y_1_1) initSize with
                | Except.ok Bool.true => return x
                | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
          [(1,
              match m_1 with
              | List.cons (Prod.mk x y) m =>
                match DecOpt.decOpt (BEq.beq y y_1_1) initSize with
                | Except.ok Bool.true => return x
                | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (Nat.succ size',
              match m_1 with
              | List.cons p m => do
                let (x_1_1 : α) ← aux_arb initSize size α_1 β_1 m y_1_1
                return x_1_1
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)])
    fun size => aux_arb size size α β m_1 y_1_1

#eval
  let P : Nat → Prop := fun n : Nat => MapFind [((2 : Nat), "foo")] n "foo"
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

-- derive_generator fun α β tys y => ∃ x, @MapsFind α β tys x y

instance [DecidableEq β] : ArbitrarySizedSuchThat α (fun x_1 => @MapsFind α β tys_1 x_1 y_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (α : Type) (β : Type) [DecidableEq β] (tys_1 : Maps α β) (y_1 : β) :
      Plausible.Gen α :=
      (match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1,
              match tys_1 with
              | List.cons m ms => do
                let (x_1 : α) ← ArbitrarySizedSuchThat.arbitrarySizedST (fun (x_1 : α) => @MapFind α β m x_1 y_1) initSize;
                return x_1
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
          [(1,
              match tys_1 with
              | List.cons m ms => do
                let (x_1 : α) ← ArbitrarySizedSuchThat.arbitrarySizedST (fun (x_1 : α) => MapFind m x_1 y_1) initSize;
                return x_1
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (Nat.succ size',
              match tys_1 with
              | List.cons m ms => do
                let (x_1 : α) ← aux_arb initSize size α β ms y_1 -- Chamelean doesn't do the right thing here: it should call itself recursively!
                return x_1
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)])
    fun size => aux_arb size size α β tys_1 y_1


#eval
  let P : Nat → Prop := fun n : Nat => MapsFind [[((2 : Nat), "foo")]] n "foo"
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10


-- derive_generator fun α β m x_1 => ∃ y_1, @MapFind α β m x_1 y_1
instance [DecidableEq α] : ArbitrarySizedSuchThat β (fun y_1_1 => @MapFind α β m_1 x_1_1 y_1_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (α : Type) (β : Type) [DecidableEq α] (m_1 : Map α β) (x_1_1 : α) :
      Plausible.Gen β :=
      (match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1,
              match m_1 with
              | List.cons (Prod.mk x y) m =>
                match DecOpt.decOpt (BEq.beq x x_1_1) initSize with
                | Except.ok Bool.true => return y
                | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
          [(1,
              match m_1 with
              | List.cons (Prod.mk x y) m =>
                match DecOpt.decOpt (BEq.beq x x_1_1) initSize with
                | Except.ok Bool.true => return y
                | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (Nat.succ size',
              match m_1 with
              | List.cons p m => do
                let (y_1_1 : β) ← aux_arb initSize size' α β m x_1_1
                return y_1_1
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)])
    fun size => aux_arb size size α β m_1 x_1_1

#eval
  let P : String → Prop := fun s : String => MapFind [((2 : Nat), "foo")] 2 s
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

/-- Creates a fresh identifier from a list -/
def getFreshIdent (pre : String) (l : List TyIdentifier) : TyIdentifier :=
if pre ∉ l then pre else
getFreshIdentSuffix l.length l
where
  getFreshIdentSuffix n l :=
  match n with
  | 0 => pre ++ "0"
  | n'+1 =>
    let ty := pre ++ (toString (l.length - n))
    if ty ∉ l then ty
    else getFreshIdentSuffix n' l

instance instArbitrarySizedSuchThatFresh [DecidableEq α] {ctx : TContext α} : ArbitrarySizedSuchThat TyIdentifier (fun a => TContext.isFresh a ctx) where
  arbitrarySizedST _ := do
    let allTypes := ctx.types.flatten.map Prod.snd
    let allTyVars := allTypes.map LTy.freeVars |>.flatten
    let pre ← Arbitrary.arbitrary
    return getFreshIdent pre allTyVars

#print TContext

#eval
  let ty := .forAll [] (LMonoTy.bool)
  let ctx := ⟨[[(⟨"foo", ()⟩, ty)]], []⟩
  let P : TyIdentifier → Prop := fun s : String => TContext.isFresh s ctx
  Gen.runUntil .none (@ArbitrarySizedSuchThat.arbitrarySizedST _ P (@instArbitrarySizedSuchThatFresh _ _ ctx) 10) 10

-- derive_checker fun α β m x => @MapNotFound α β m x
instance [DecidableEq α_1] : DecOpt (@MapNotFound α_1 β_1 m_1 x_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (α : Type) (β : Type) [DecidableEq α] (m_1 : Map α β) (x_1 : α) :
      Except Plausible.GenError Bool :=
      (match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun (_ : Unit) =>
            match m_1 with
            | List.nil => Except.ok Bool.true
            | _ => Except.ok Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun (_ : Unit) =>
            match m_1 with
            | List.nil => Except.ok Bool.true
            | _ => Except.ok Bool.false,
            fun (_ : Unit) =>
            match m_1 with
            | List.cons (Prod.mk z w) m =>
              DecOpt.andOptList [aux_dec initSize size' α β m x_1, DecOpt.decOpt (Ne x_1 z) initSize]
            | _ => Except.ok Bool.false])
    fun size => aux_dec size size α_1 β_1 m_1 x_1

#eval DecOpt.decOpt (MapNotFound [("foo", 4)] "foo") 5
#eval DecOpt.decOpt (MapNotFound [("foo", 4)] "bar") 5

-- derive_generator fun α β m x_1_1 ty_1_1 => ∃ m', @MapReplace α β m x_1_1 ty_1_1 m'
instance [DecidableEq α] : ArbitrarySizedSuchThat (Map α β) (fun m'_1 => @MapReplace α β m_1 x_1_1_1 ty_1_1_1 m'_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (α : Type) (β : Type) [DecidableEq α] (m_1 : Map α β) (x_1_1_1 : α)
      (ty_1_1_1 : β) : Plausible.Gen (Map α β) :=
      (match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1,
              match m_1 with
              | List.nil => return List.nil
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1,
              match m_1 with
              | List.cons (Prod.mk x z) m =>
                match DecOpt.decOpt (BEq.beq x x_1_1_1) initSize with
                | Except.ok Bool.true => return List.cons (Prod.mk x_1_1_1 ty_1_1_1) m
                | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
          [(1,
              match m_1 with
              | List.nil => return List.nil
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1,
              match m_1 with
              | List.cons (Prod.mk x z) m =>
                match DecOpt.decOpt (BEq.beq x x_1_1_1) initSize with
                | Except.ok Bool.true => return List.cons (Prod.mk x_1_1_1 ty_1_1_1) m
                | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (Nat.succ size',
              match m_1 with
              | List.cons (Prod.mk z w) m =>
                match DecOpt.decOpt (Ne x_1_1_1 z) initSize with
                | Except.ok Bool.true => do
                  let (m' : Map α β) ← aux_arb initSize size' α β m x_1_1_1 ty_1_1_1
                  return List.cons (Prod.mk z w) m'
                | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)])
    fun size => aux_arb size size α β m_1 x_1_1_1 ty_1_1_1

#eval
  let P : Map Nat String → Prop := fun m' => MapReplace [((2 : Nat), "old")] 2 "new" m'
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

-- derive_checker fun α β m x => @MapsNotFound α β m x

instance [DecidableEq α_1] : DecOpt (@MapsNotFound α_1 β_1 m_1 x_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (α : Type) (β : Type) [DecidableEq α] (m_1 : Maps α β) (x_1 : α) :
      Except Plausible.GenError Bool :=
      (match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun (_ : Unit) =>
            match m_1 with
            | List.nil => Except.ok Bool.true
            | _ => Except.ok Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun (_ : Unit) =>
            match m_1 with
            | List.nil => Except.ok Bool.true
            | _ => Except.ok Bool.false,
            fun (_ : Unit) =>
            match m_1 with
            | List.cons m ms =>
              DecOpt.andOptList [aux_dec initSize size' α β ms x_1, DecOpt.decOpt (MapNotFound m x_1) initSize]
            | _ => Except.ok Bool.false])
    fun size => aux_dec size size α_1 β_1 m_1 x_1


#eval DecOpt.decOpt (MapsNotFound [[("foo", 4)]] "foo") 5
#eval DecOpt.decOpt (MapsNotFound [[("foo", 4)]] "bar") 5

-- derive_generator fun α β tys_1 x_1 ty_1 => ∃ (Γ_1 : Maps α β), @MapsReplace α β tys_1 x_1 ty_1 Γ_1
instance [DecidableEq α] : ArbitrarySizedSuchThat (Maps α β) (fun Γ_1_1 => @MapsReplace α β tys_1_1 x_1_1 ty_1_1 Γ_1_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (α : Type) (β : Type) [DecidableEq α] (tys_1_1 : Maps α β) (x_1_1 : α)
      (ty_1_1 : β) : Plausible.Gen (Maps α β) :=
      (match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1,
              match tys_1_1 with
              | List.nil => return List.nil
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
          [(1,
              match tys_1_1 with
              | List.nil => return List.nil
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (Nat.succ size',
              match tys_1_1 with
              | List.cons m ms => do
                let (m' : Map α β) ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun (m' : Map α β) => @MapReplace α β m x_1_1 ty_1_1 m') initSize;
                do
                  let (ms' : Maps α β) ←
                    aux_arb initSize size α β ms x_1_1 ty_1_1
                  return List.cons m' ms'
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)])
    fun size => aux_arb size size α β tys_1_1 x_1_1 ty_1_1

#eval
  let P : Maps Nat String → Prop := fun m' => MapsReplace [[((2 : Nat), "old")]] 2 "new" m'
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

-- derive_generator (fun α β tys_1 x_1 => ∃ (z : β), @MapsFind α β tys_1 x_1 z)
instance [DecidableEq α][DecidableEq β] : ArbitrarySizedSuchThat β (fun z_1 => @MapsFind α β tys_1_1 x_1_1 z_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (α : Type) (β : Type) [DecidableEq α] [DecidableEq β] (tys_1_1 : Maps α β) (x_1_1 : α) :
      Plausible.Gen β :=
      (match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1,
              match tys_1_1 with
              | List.cons m ms => do
                let (z_1 : β) ← ArbitrarySizedSuchThat.arbitrarySizedST (fun (z_1 : β) => MapFind m x_1_1 z_1) initSize;
                return z_1
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
          [(1,
              match tys_1_1 with
              | List.cons m ms => do
                let (z_1 : β) ← ArbitrarySizedSuchThat.arbitrarySizedST (fun (z_1 : β) => MapFind m x_1_1 z_1) initSize;
                return z_1
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (Nat.succ size',
              match tys_1_1 with
              | List.cons m ms => do
                let (z_1 : β) ← aux_arb initSize size' α β ms x_1_1
                return z_1
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)])
    fun size => aux_arb size size α β tys_1_1 x_1_1

#eval
  let P : _ → Prop := fun z => MapsFind [[((2 : Nat), "old")]] 2 z
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

-- derive_generator (fun α β tys x ty => ∃ Γ, @MapsInsert α β tys x ty Γ)

instance [DecidableEq α] [DecidableEq β] : ArbitrarySizedSuchThat (Maps α β) (fun Γ_1 => @MapsInsert α β tys_1 x_1 ty_1 Γ_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (α_1 : Type) (β_1 : Type) (tys_1 : Maps α β) (x_1 : α)
      (ty_1 : β) : Plausible.Gen (Maps α β) :=
      (match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1, do
              let (z : β) ← ArbitrarySizedSuchThat.arbitrarySizedST (fun (z : β) => MapsFind tys_1 x_1 z) initSize;
              do
                let (Γ_1 : Maps α β) ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun (Γ_1 : Maps α β) => MapsReplace tys_1 x_1 ty_1 Γ_1)
                      initSize;
                return Γ_1),
            (1,
              match tys_1 with
              | List.cons m ms =>
                match DecOpt.decOpt (MapsNotFound (List.cons m ms) x_1) initSize with
                | Except.ok Bool.true => return List.cons (List.cons (Prod.mk x_1 ty_1) m) ms
                | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
          [(1, do
              let (z : β) ← ArbitrarySizedSuchThat.arbitrarySizedST (fun (z : β) => MapsFind tys_1 x_1 z) initSize;
              do
                let (Γ_1 : Maps α β) ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun (Γ_1 : Maps α β) => MapsReplace tys_1 x_1 ty_1 Γ_1)
                      initSize;
                return Γ_1),
            (1,
              match tys_1 with
              | List.cons m ms =>
                match DecOpt.decOpt (MapsNotFound (List.cons m ms) x_1) initSize with
                | Except.ok Bool.true => return List.cons (List.cons (Prod.mk x_1 ty_1) m) ms
                | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            ])
    fun size => aux_arb size size α β tys_1 x_1 ty_1

-- derive_generator fun (α β : Type) Γ => ∃ (p : α × β), @MapFind₂ α β Γ p

instance [Plausible.Arbitrary α_1] [DecidableEq α_1] [Plausible.Arbitrary β_1] [DecidableEq β_1] :
    ArbitrarySizedSuchThat (α_1 × β_1) (fun p_1 => @MapFind₂ α_1 β_1 Γ_1 p_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (α_1 : Sort _) (β_1 : Sort _) (Γ_1 : Map α_1 β_1)
      [Plausible.Arbitrary α_1] [DecidableEq α_1] [Plausible.Arbitrary β_1] [DecidableEq β_1] :
      Plausible.Gen (α_1 × β_1) :=
      (match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1,
              match Γ_1 with
              | List.cons (Prod.mk x y) m => return Prod.mk x y
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
          [(1,
              match Γ_1 with
              | List.cons (Prod.mk x y) m => return Prod.mk x y
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (Nat.succ size',
              match Γ_1 with
              | List.cons p m => do
                let (p_1 : Prod α_1 β_1) ← aux_arb initSize size' α_1 β_1 m;
                return p_1
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)])
    fun size => aux_arb size size α_1 β_1 Γ_1


-- derive_generator fun (α β : Type) Γ => ∃ (p : α × β), @MapsFind₂ α β Γ p


instance [Plausible.Arbitrary α_1] [DecidableEq α_1] [Plausible.Arbitrary β_1] [DecidableEq β_1] :
    ArbitrarySizedSuchThat (α_1 × β_1) (fun p_1 => @MapsFind₂ α_1 β_1 Γ_1 p_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (α_1 : Sort _) (β_1 : Sort _) (Γ_1 : Maps α_1 β_1)
      [Plausible.Arbitrary α_1] [DecidableEq α_1] [Plausible.Arbitrary β_1] [DecidableEq β_1] :
      Plausible.Gen (α_1 × β_1) :=
    match size with
    | 0 =>
      match Γ_1 with
      | m :: _ => ArbitrarySizedSuchThat.arbitrarySizedST (fun p => MapFind₂ m p) initSize
      | _ => throw Plausible.Gen.genericFailure
    | size' + 1 => -- Slight hand optimization here, where we can match on Γ_1 directly
      match Γ_1 with
      | m :: ms => GeneratorCombinators.backtrack
        [
          (1, ArbitrarySizedSuchThat.arbitrarySizedST (fun p => MapFind₂ m p) initSize),
          (1, aux_arb initSize size' α_1 β_1 ms)
        ]
      | _ => throw Plausible.Gen.genericFailure
  fun size => aux_arb size size α_1 β_1 Γ_1


#eval
  let P : Maps Nat String → Prop := fun m' => MapsInsert [[((2 : Nat), "old")]] 2 "new" m'
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

#eval
  let P : Maps Nat String → Prop := fun m' => MapsInsert [[], [((2 : Nat), "old")]] 2 "new" m'
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

#eval
  let P : Maps Nat String → Prop := fun m' => MapsInsert [[], [((3 : Nat), "old")]] 2 "new" m'
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

-- -- Some funky bug
-- set_option trace.plausible.deriving.arbitrary true in
-- derive_generator (fun fact ctx ty => ∃ t, HasType fact ctx t ty)

instance : ArbitrarySizedSuchThat (LExpr LMonoTy Unit) (fun t_1 => HasType fact_1 ctx_1 t_1 ty_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (ctx_1 : TContext Unit) (ty_1 : LTy) :
      Plausible.Gen (LExpr LMonoTy Unit) :=
      (match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1,
              match ty_1 with
              | Lambda.LTy.forAll (List.nil) .bool =>
                return .boolConst true
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1,
              match ty_1 with
              | Lambda.LTy.forAll (List.nil) .bool =>
                return .boolConst false
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1,
              match ty_1 with
              | Lambda.LTy.forAll (List.nil) .int => do
                let n ← Arbitrary.arbitrary
                return .intConst n
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1, do
                let (x : Identifier Unit × LTy) ←
                  ArbitrarySizedSuchThat.arbitrarySizedST
                      (fun x => MapsFind₂ (Lambda.TContext.types ctx_1) x) initSize;
                if x.snd = ty_1 then
                  return Lambda.LExpr.fvar x.fst (.some <| LTy.toMonoTypeUnsafe ty_1)
                else
                  throw Gen.genericFailure
            )
            ]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
        [
          (1,
              match ty_1 with
              | Lambda.LTy.forAll (List.nil) .bool =>
                return .boolConst true
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1,
              match ty_1 with
              | Lambda.LTy.forAll (List.nil) .bool =>
                return .boolConst false
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1,
              match ty_1 with
              | Lambda.LTy.forAll (List.nil) .int => do
                let n ← Arbitrary.arbitrary
                return .intConst n
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (size', do
                let (x : Identifier Unit × LTy) ←
                  ArbitrarySizedSuchThat.arbitrarySizedST
                      (fun x_x_ty => MapsFind₂ (Lambda.TContext.types ctx_1) x_x_ty) initSize;
                  if x.snd = ty_1 then
                  return Lambda.LExpr.fvar x.fst (.some <| LTy.toMonoTypeUnsafe ty_1)
                else
                  throw Gen.genericFailure),
            -- (Nat.succ size', do
            --   let (e : LExpr LMonoTy Unit) ← aux_arb initSize size' ctx_1 ty_1;
            --   do
            --     let (info : Info) ← Plausible.Arbitrary.arbitrary;
            --     return Lambda.LExpr.mdata info e),
            (Nat.succ size',
              match ty_1 with
              |
              Lambda.LTy.forAll (List.nil)
                  (Lambda.LMonoTy.tcons "arrow"
                    (List.cons (x_ty)
                      (List.cons (e_ty) (List.nil)))) => do
                let x : Identifier Unit ← Arbitrary.arbitrary
                let x_ty' := LTy.forAll [] x_ty
                let e_ty' := LTy.forAll [] e_ty
                let Γ' : Maps (Identifier Unit) LTy ←
                    ArbitrarySuchThat.arbitraryST
                        (fun (Γ' : Maps (Identifier Unit) LTy) =>
                          MapsInsert (Lambda.TContext.types ctx_1) x x_ty' Γ')
                let e ← aux_arb initSize size' {ctx_1 with types := Γ'} e_ty'
                let e := varClose 0 x e
                return .abs x_ty e
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (Nat.succ size', do
              let (t2 : LMonoTy) ← Plausible.Arbitrary.arbitrary;
              do
                let (e2 : LExpr LMonoTy Unit) ← aux_arb initSize size' ctx_1 (.forAll [] t2);
                do
                  if h1 : isMonoType ty_1 then
                  let (e1 : LExpr LMonoTy Unit) ←
                    aux_arb initSize size' ctx_1
                            (Lambda.LTy.forAll (List.nil)
                              (Lambda.LMonoTy.tcons "arrow"
                                (List.cons (t2)
                                  (List.cons (Lambda.LTy.toMonoType ty_1 h1) (List.nil)))));
                      return Lambda.LExpr.app e1 e2
                  else MonadExcept.throw Plausible.Gen.genericFailure),
            (Nat.succ size', do
              let (c : LExpr LMonoTy Unit) ←
                aux_arb initSize size' ctx_1 (Lambda.LTy.forAll (List.nil) (Lambda.LMonoTy.tcons "bool" (List.nil)));
              do
                let (e1 : LExpr LMonoTy Unit) ← aux_arb initSize size' ctx_1 ty_1;
                do
                  let (e2 : LExpr LMonoTy Unit) ← aux_arb initSize size' ctx_1 ty_1;
                  return Lambda.LExpr.ite c e1 e2),
            (Nat.succ size',
              match ty_1 with
              | Lambda.LTy.forAll (List.nil) (Lambda.LMonoTy.tcons "bool" (List.nil)) => do
                let (ty : LTy) ← Plausible.Arbitrary.arbitrary;
                do
                  let (e1 : LExpr LMonoTy Unit) ← aux_arb initSize size' ctx_1 ty;
                  do
                    let (e2 : LExpr LMonoTy Unit) ← aux_arb initSize size' ctx_1 ty;
                    return Lambda.LExpr.eq e1 e2
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (10, do
              let (f : LFunc Unit) ←
                @ArbitrarySizedSuchThat.arbitrarySizedST _
                    (fun (f : LFunc Unit) =>
                      @ArrayFind (@Lambda.LFunc (@Unit)) (@Lambda.LContext.functions (@Unit) fact_1) f)
                    _ initSize;
              do
                match f.type with
                | .ok f_ty =>
                  if f_ty  = ty_1 then
                    return Lambda.LExpr.op f.name (Option.none)
                  else throw Plausible.Gen.genericFailure
                | _ => throw Plausible.Gen.genericFailure
                )
        ])
    fun size => aux_arb size size ctx_1 ty_1

#print LContext
#print Factory

#eval Gen.printSamples (Arbitrary.arbitrary : Gen LMonoTy)

def knownTypes : KnownTypes := Std.HashMap.ofList [⟨"bool", 0⟩, ⟨"int", 0⟩, ⟨"arrow", 2⟩]


#print KnownTypes.default
-- FIXME: get the boogie factory
abbrev example_lctx : LContext Unit :=
{ LContext.empty with knownTypes := KnownTypes.default
                      functions := Lambda.IntBoolFactory
}

abbrev example_ctx : TContext Unit := ⟨[[]], []⟩
-- abbrev example_ty : LTy := .forAll [] <| .tcons "bool" []
abbrev example_ty : LTy := .forAll [] <| .tcons "arrow" [.tcons "bool" [], .tcons "bool" []]

#eval
  let P : Maps (Identifier Unit) LTy → Prop := fun Γ => MapsInsert (example_ctx.types) "y" (.forAll [] (.tcons "int" [])) Γ
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 4) 4


#print String
#print Char

#eval varClose 0 "x" (.fvar "x" (.some <| .tcons "bool" []))

#print TEnv
#print TGenEnv
#print TState
#print Factory
#print KnownTypes
#print KnownType
#print Identifiers
#print Std.HashMap


#check List.range

#time #eval
    let P : LExpr LMonoTy Unit → Prop := fun t => HasType example_lctx example_ctx t example_ty
    Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 4) 4

#print LState

#check LState.init.config

-- { σ with config := { σ.config with factory := newF } }
def example_lstate :=
  { LState.init (IDMeta := Unit) with config :=
    { LState.init.config (IDMeta := Unit) with
      factory := Lambda.IntBoolFactory }
  }

#eval LExpr.eval 100 example_lstate <| .app (.abs .none (.bvar 0)) (.const <| .boolConst true)


#print LExpr
#print Shrinkable
#print IdentT
#print Identifier

instance [Inhabited β] : Shrinkable (LExpr α β) where
  shrink t :=
  let rec aux (t : LExpr α β) : List (LExpr α β) :=
  match t with
    | .fvar _ _
    | .bvar _
    | .op _ _
    | .const _ -- We're being a bit lazy here for the time being
              => []
    | .app t u =>
      t :: u :: (.app <$> aux t <*> aux u)
    | .abs ty t => (LExpr.varOpen 0 ⟨⟨"x", default⟩, ty⟩ t) :: (.abs ty <$> aux t) -- IDK about the `"x"`
    | .eq t u => t :: u :: (.eq <$> aux t <*> aux u)
    | .ite cond t u => cond :: t :: u :: (.ite <$> aux cond <*> aux t <*> aux u)
    | .quant k ty tr t => (LExpr.varOpen 0 ⟨⟨"x", default⟩, ty⟩ t) :: (.quant k ty tr <$> aux t)
    | .mdata i t => t :: (.mdata i <$> aux t)
  aux t

#check List.find?
#print TState
-- Shrinks an element of `α` recursively.
partial def shrinkFunAux [Shrinkable α] (f : α → Bool) (x : α) : Option α := do
  let candidates := Shrinkable.shrink x
  let y ← candidates.find? f
  let z := shrinkFunAux f y
  z <|> some y

def shrinkFun [Shrinkable α] (f : α → Bool) (x : α) : α :=
let shrinked := shrinkFunAux f x
match shrinked with
| .some y => y
| .none => x

#eval Shrinkable.shrink (LExpr.eq (TypeType := Unit) (IDMeta := Unit) (.fvar "x" .none) (.fvar "y" .none))

#eval shrinkFun (fun n : Nat => n % 3 == 2) 42

def canAnnotate (t : LExpr LMonoTy Unit) : Bool :=
    let state : TState := {}
  let env : TEnv Unit := { genEnv := ⟨example_ctx, state⟩ }
  let t' := LExpr.annotate example_lctx env t
  t'.isOk

#print Factory
#print LFunc

#time #eval do
  IO.println s!"Generating terms of type\n{example_ty}\nin context\n{repr example_ctx}\nin \
                factory\n{example_lctx.functions.map (fun f : LFunc Unit => f.name)}\n"
  for i in List.range 100 do
    let P : LExpr LMonoTy Unit → Prop := fun t => HasType example_lctx example_ctx t example_ty
    let t ← Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 5) 5
    -- IO.println s!"Generated {t}"
    if !(canAnnotate t) then
      IO.println s!"FAILED({i}): {t}\n\nSHRUNK TO:\n{shrinkFun (not ∘ canAnnotate) t}\n\n"


structure MyPair where
  first : Nat
  second : Nat
deriving Arbitrary, Inhabited

opaque f : MyPair → MyPair

inductive MyPred : MyPair → Prop where
-- | foo : MyPred p
| bar : MyPred p → MyPred p
-- | baz : 0 = 0 → MyPred p
-- | boz : MyPred ⟨p.first, p.second⟩ → MyPred p
-- | biz : MyPred (f p) → MyPred p
-- | fresh  {n'} {p : MyPair} : n' = 0 → MyPred {p with second := n'} → MyPred p


#check ∃ p : MyPair, MyPred p
derive_generator ∃ p : MyPair, MyPred p

opaque F : Nat → Type

structure C where
  fld : Nat

opaque unF : ∀ x, F x → Nat

inductive Foo : C → Prop where
| dummy : Foo ⟨ 0 ⟩
| constr {c : C} : Foo { c with fld := a' } → Foo ⟨ (a * 2) + 1 ⟩

derive_generator ∃ c, Foo c

#print Info
#print QuantifierKind
#print LConst
#print LMonoTy
#print LTy
#print LExpr
#print TContext
#print Maps
#print Map
#print TypeAlias
#print Identifier
#print TyIdentifier

opaque toMono : LTy → LMonoTy

def varClose' : LExpr LMonoTy Unit → LExpr LMonoTy Unit :=
  fun e => e


inductive HasType' : (TContext Unit) → (LExpr LMonoTy Unit) → LTy → Prop where

  | tabs : ∀ Γ Γ' e e_ty,
            new_ty = toMono e_ty →
            HasType' { Γ with types := Γ'} e e_ty →
            HasType' Γ (.abs .none <| varClose' e)
                        (.forAll [] (.tcons z [new_ty]))

-- set_option trace.plausible.deriving.arbitrary true in
derive_generator fun ct ty => ∃ e, HasType' ct e ty
