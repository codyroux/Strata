import Strata.DL.Imperative.CmdSemantics
import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.LExprTypeSpec
import Strata.DL.Lambda.LExprTypeEnv
import Strata.DL.Lambda.LExprWF
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

instance [Decidable P] : DecOpt P := by infer_instance

instance : DecidableEq Arith.Expr := by infer_instance

#print Lambda.LExpr
#print Lambda.Info
#print Lambda.QuantifierKind

deriving instance Arbitrary for Lambda.Identifier
deriving instance Arbitrary for Lambda.Info
deriving instance Arbitrary for Lambda.QuantifierKind

deriving instance Arbitrary for Lambda.LExpr

#eval Gen.printSamples (Arbitrary.arbitrary : Gen <| Lambda.LExpr String String)

#print Lambda.TContext

#print Lambda.LExpr.HasType

-- derive_generator (fun idMeta inst ctx ty => ∃ t, @Lambda.LExpr.HasType idMeta inst ctx t ty)

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

#print TContext
#print Maps
#print Map
#print Maps.find?

inductive MapFind : Map α β → α → β → Prop where
| hd : MapFind ((x, y) :: m) x y
| tl : MapFind m x y → MapFind (p :: m) x y

inductive MapsFind : Maps α β → α → β → Prop where
| hd : MapFind m x y → MapsFind (m :: ms) x y
| tl : MapsFind ms x y → MapsFind (m :: ms) x y

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


instance instStringSuchThatIsInt : ArbitrarySizedSuchThat String (fun s => s.isInt) where
  arbitrarySizedST _ := toString <$> (Arbitrary.arbitrary : Gen Int)


inductive HasType : (TContext Unit) → (LExpr LMonoTy Unit) → LTy → Prop where
  | tmdata : ∀ Γ info e ty, HasType Γ e ty →
                            HasType Γ (.mdata info e) ty

  | tbool_const_t : ∀ Γ, HasType Γ (.const "true" none)
                         (.forAll [] (.tcons "bool" []))
  | tbool_const_f : ∀ Γ, HasType Γ (.const "false" none)
                        (.forAll [] (.tcons "bool" []))
  | tint_const : ∀ Γ, n.isInt → HasType Γ (.const n none)
                                (.forAll [] (.tcons "int" []))

  | tvar : ∀ Γ x ty, MapsFind Γ.types x y → HasType Γ (.fvar x none) ty

  | tabs : ∀ Γ x x_ty e e_ty,
            LExpr.fresh x e →
            (hx : LTy.isMonoType x_ty) →
            (he : LTy.isMonoType e_ty) →
            MapsInsert Γ.types x.fst x_ty Γ' →
            HasType { Γ with types := Γ'} (LExpr.varOpen 0 x e) e_ty →
            HasType Γ (.abs .none e)
                      (.forAll [] (.tcons "arrow" [(LTy.toMonoType x_ty hx),
                                                   (LTy.toMonoType e_ty he)]))

--  | tcons_intro : ∀ Γ C args targs,
--                  args.length == targs.length →
--                  ∀ et ∈ (List.zip args targs), HasType Γ et.fst et.snd →
--                  HasType Γ (.app (.const C .none) args) (.tcons C targs)

--  | tcons_elim :
--                HasType Γ (.app (.const C) args) (.tcons C targs) →
--                (h : i < targs.length) →
--                HasType Γ (.proj i args) (List.get targs i h)

  | tapp : ∀ Γ e1 e2 t1 t2,
            (h1 : LTy.isMonoType t1) →
            (h2 : LTy.isMonoType t2) →
            HasType Γ e1 (.forAll [] (.tcons "arrow" [(LTy.toMonoType t2 h2),
                                                     (LTy.toMonoType t1 h1)])) →
            HasType Γ e2 t2 →
            HasType Γ (.app e1 e2) t1

  -- `ty` is more general than `e_ty`, so we can instantiate `ty` with `e_ty`.
  | tinst : ∀ Γ e ty e_ty x x_ty,
           HasType Γ e ty →
           e_ty = LTy.open x x_ty ty →
           HasType Γ e e_ty

  -- The generalization rule will let us do things like the following:
  -- `(·ftvar "a") → (.ftvar "a")` (or `a → a`) will be generalized to
  -- `(.btvar 0) → (.btvar 0)` (or `∀a. a → a`), assuming `a` is not in the
  -- context.
  | tgen : ∀ Γ e a ty,
           HasType Γ e ty →
           TContext.isFresh a Γ →
           HasType Γ e (LTy.close a ty)

  | tif : ∀ Γ c e1 e2 ty,
          HasType Γ c (.forAll [] (.tcons "bool" [])) →
          HasType Γ e1 ty →
          HasType Γ e2 ty →
          HasType Γ (.ite c e1 e2) ty

  | teq : ∀ Γ e1 e2 ty,
          HasType Γ e1 ty →
          HasType Γ e2 ty →
          HasType Γ (.eq e1 e2) (.forAll [] (.tcons "bool" []))

deriving instance Arbitrary for LMonoTy

set_option trace.plausible.deriving.arbitrary true in
deriving instance Arbitrary for LTy

#eval Gen.printSamples (Arbitrary.arbitrary : Gen LMonoTy)

-- inductive Total {α} : α → Prop where
-- | any a : Total a

-- derive_generator fun α => ∃ a, @Total α a

derive_generator fun α β m y_1 => ∃ x_1, @MapFind α β m x_1 y_1

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
                  -- ArbitrarySizedSuchThat.arbitrarySizedST (fun (x_1_1 : α) => MapFind m x_1_1 y_1_1) initSize;
                return x_1_1
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)])
    fun size => aux_arb size size α β m_1 y_1_1

#eval Gen.printSamples (ArbitrarySizedSuchThat.arbitrarySizedST (fun x => @MapFind Nat String [(2, "foo")] x "foo") 5)

derive_generator fun α β tys y => ∃ x, @MapsFind α β tys x y

instance [BEq β] : ArbitrarySizedSuchThat α (fun x_1 => @MapsFind α β tys_1 x_1 y_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (α_1 : Type) (β_1 : Type) (tys_1 : Maps α β) (y_1 : β) :
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
                let (x_1 : α) ← aux_arb size size α β ms y_1 -- Chamelean doesn't do the right thing here
                return x_1
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)])
    fun size => aux_arb size size α β tys_1 y_1

instance [BEq β] : ArbitrarySizedSuchThat α (fun x_1 => @MapsFind α β tys_1 x_1 y_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (α_1 : Type) (β_1 : Type) (tys_1 : Maps α β) (y_1 : β) :
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
                let (x_1 : α) ← ArbitrarySizedSuchThat.arbitrarySizedST (fun (x_1 : α) => MapsFind ms x_1 y_1) initSize;
                return x_1
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)])
    fun size => aux_arb size size α β tys_1 y_1

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

instance {ctx : TContext Unit} : ArbitrarySizedSuchThat TyIdentifier (fun a => TContext.isFresh a ctx) where
  arbitrarySizedST _ := do
    let allTypes := ctx.types.flatten.map Prod.snd
    let allTyVars := allTypes.map LTy.freeVars |>.flatten
    let pre ← Arbitrary.arbitrary
    return getFreshIdent pre allTyVars

derive_generator (fun ctx ty => ∃ t, HasType ctx t ty)

instance : ArbitrarySizedSuchThat (LExpr LMonoTy Unit) (fun t_1 => HasType ctx_1 t_1 ty_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (ctx_1 : TContext Unit) (ty_1 : LTy) :
      Plausible.Gen (LExpr LMonoTy Unit) :=
      (match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1,
              match ty_1 with
              | Lambda.LTy.forAll (List.nil) (Lambda.LMonoTy.tcons "bool" (List.nil)) =>
                return Lambda.LExpr.const "true" (Option.none)
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1,
              match ty_1 with
              | Lambda.LTy.forAll (List.nil) (Lambda.LMonoTy.tcons "bool" (List.nil)) =>
                return Lambda.LExpr.const "false" (Option.none)
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1,
              match ty_1 with
              | Lambda.LTy.forAll (List.nil) (Lambda.LMonoTy.tcons "int" (List.nil)) => do
                let vn ← ArbitrarySizedSuchThat.arbitrarySizedST (fun vn => Eq vn (Bool.true)) initSize;
                match vn with
                  | String.isInt n => return Lambda.LExpr.const n (Option.none)
                  | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1, do
              let (y : LTy) ← Plausible.Arbitrary.arbitrary;
              do
                let (x : Identifier Unit) ←
                  ArbitrarySizedSuchThat.arbitrarySizedST
                      (fun (x : Identifier Unit) => MapsFind (Lambda.TContext.types ctx_1) x y) initSize;
                return Lambda.LExpr.fvar x (Option.none))]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
          [(1,
              match ty_1 with
              | Lambda.LTy.forAll (List.nil) (Lambda.LMonoTy.tcons "bool" (List.nil)) =>
                return Lambda.LExpr.const "true" (Option.none)
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1,
              match ty_1 with
              | Lambda.LTy.forAll (List.nil) (Lambda.LMonoTy.tcons "bool" (List.nil)) =>
                return Lambda.LExpr.const "false" (Option.none)
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1,
              match ty_1 with
              | Lambda.LTy.forAll (List.nil) (Lambda.LMonoTy.tcons "int" (List.nil)) => do
                let vn ← ArbitrarySizedSuchThat.arbitrarySizedST (fun vn => Eq vn (Bool.true)) initSize;
                match vn with
                  | String.isInt n => return Lambda.LExpr.const n (Option.none)
                  | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1, do
              let (y : LTy) ← Plausible.Arbitrary.arbitrary;
              do
                let (x : Identifier Unit) ←
                  ArbitrarySizedSuchThat.arbitrarySizedST
                      (fun (x : Identifier Unit) => MapsFind (Lambda.TContext.types ctx_1) x y) initSize;
                return Lambda.LExpr.fvar x (Option.none)),
            (Nat.succ size', do
              let (e : LExpr LMonoTy Unit) ← aux_arb initSize size' ctx_1 ty_1;
              do
                let (info : Info) ← Plausible.Arbitrary.arbitrary;
                return Lambda.LExpr.mdata info e),
            (Nat.succ size',
              match ty_1 with
              |
              Lambda.LTy.forAll (List.nil)
                  (Lambda.LMonoTy.tcons "arrow"
                    (List.cons (Lambda.LTy.toMonoType x_ty hx)
                      (List.cons (Lambda.LTy.toMonoType e_ty he) (List.nil)))) =>
                do
                let vx_e ← ArbitrarySizedSuchThat.arbitrarySizedST (fun vx_e => Eq vx_e (Bool.true)) initSize;
                match vx_e with
                  | Lambda.LExpr.fresh (instDecidableEqPUnit) x e => do
                    let (Γ' : Maps (Identifier Unit) LTy) ←
                      ArbitrarySizedSuchThat.arbitrarySizedST
                          (fun (Γ' : Maps (Identifier Unit) LTy) =>
                            MapsInsert (Lambda.TContext.types ctx_1) (Prod.fst x) x_ty Γ')
                          initSize;
                    match
                        DecOpt.decOpt
                          (HasType (Lambda.TContext.mk Γ' (Lambda.TContext.aliases ctx_1))
                            (Lambda.LExpr.varOpen (OfNat.ofNat 0) x e) e_ty)
                          initSize with
                      | Except.ok Bool.true => return Lambda.LExpr.abs (Option.none) e
                      | _ => MonadExcept.throw Plausible.Gen.genericFailure
                  | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (Nat.succ size', do
              let (t2 : LTy) ← Plausible.Arbitrary.arbitrary;
              do
                let (e2 : LExpr LMonoTy Unit) ← aux_arb initSize size' ctx_1 t2;
                do
                  let (h2 : Eq Bool (isMonoType t2) true) ← Plausible.Arbitrary.arbitrary;
                  do
                    let (h1 : Eq Bool (isMonoType ty_1) true) ← Plausible.Arbitrary.arbitrary;
                    do
                      let (e1 : LExpr LMonoTy Unit) ←
                        aux_arb initSize size' ctx_1
                            (Lambda.LTy.forAll (List.nil)
                              (Lambda.LMonoTy.tcons "arrow"
                                (List.cons (Lambda.LTy.toMonoType t2 h2)
                                  (List.cons (Lambda.LTy.toMonoType ty_1 h1) (List.nil)))));
                      return Lambda.LExpr.app e1 e2),
            (Nat.succ size', do
              let vx_x_ty_ty ← ArbitrarySizedSuchThat.arbitrarySizedST (fun vx_x_ty_ty => Eq ty_1 vx_x_ty_ty) initSize;
              match vx_x_ty_ty with
                | LTy.open x x_ty ty => do
                  let (t_1 : LExpr LMonoTy Unit) ← aux_arb initSize size' ctx_1 ty;
                  return t_1
                | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (Nat.succ size', do
              let (a : TyIdentifier) ←
                ArbitrarySizedSuchThat.arbitrarySizedST
                    (fun (a : TyIdentifier) => @Lambda.TContext.isFresh _ (instDecidableEqPUnit) a ctx_1) initSize;
              do
                let (ty : LTy) ← Plausible.Arbitrary.arbitrary;
                do
                  let (t_1 : LExpr LMonoTy Unit) ← aux_arb initSize size' ctx_1 ty;
                  do
                    let (ty_1 : LTy) ←
                      ArbitrarySizedSuchThat.arbitrarySizedST (fun (ty_1 : LTy) => Eq ty_1 (LTy.close a ty)) initSize;
                    return t_1),
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
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)])
    fun size => aux_arb size size ctx_1 ty_1
