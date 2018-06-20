Require Import Utf8.
From Coq Require Import ssreflect ssrnat ssrbool ssrfun seq.

Require Import core.

Generalizable All Variables.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

(******************************************************************************)

Notation "∄  x .. y , P" := (¬ (∃ x, .. (∃ y, P) ..))
  (at level 200, x binder, y binder, right associativity) : type_scope.

(******************************************************************************)

Instance Num_nat__ : Num nat := {| core.__op_zp__ := addn
                                 ; core.__op_zm__ := subn
                                 ; core.__op_zt__ := muln
                                 ; abs            := id
                                 ; fromInteger    := BinInt.Z.to_nat
                                 ; negate         := fun _ => 0
                                 ; signum         := fun n => match n with
                                                       | O   => 0
                                                       | S _ => 1
                                                     end |}.
Instance Num_Int__ : Num Int. Admitted.

(******************************************************************************)

Infix "∈" := List.In (at level 40).

Fixpoint indices_from {A} {B} `{Num A} (z : A) (s : list B) : list A :=
  match s with
    | [::]    => [::]
    | x :: s' => z :: indices_from (z + #1) s'
  end.

Definition indices {A} {B} `{Num B} : list A → list B := indices_from #0.

Theorem indices_from_is_iota {A} (z : nat) (s : list A) :
  indices_from z s = iota z (length s).
Proof. by elim: s z => [|a s IH] z //=; rewrite /BinPos.Pos.to_nat /= addn1 IH. Qed.

Theorem indices_is_iota {A} (s : list A) :
  indices s = iota 0 (length s).
Proof. by rewrite -indices_from_is_iota. Qed.

Fixpoint zip_with {A} {B} {C} (f : A → B → C) (s : list A) (t : list B) : list C :=
  match s , t with
    | a :: s' , b :: t' => f a b :: zip_with f s' t'
    | _       , _       => [::]
  end.

Theorem zip_with_is_zip {A} {B} :
  zip_with (@pair A B) =2 zip.
Proof. by elim => [|a s IH] [|b t] //=; rewrite IH. Qed.

Theorem map_zip_is_zip_with {A} {B} {C} (f : A → B → C) s t :
  zip_with f s t = map (prod_curry f) (zip s t).
Proof. by elim: s t => [|a s IH] [|b t] //=; rewrite IH. Qed.

Theorem map_zip_is_zip_with' {A} {B} {C} (f : A * B → C) s t :
  zip_with (prod_uncurry f) s t = map f (zip s t).
Proof. by elim: s t => [|a s IH] [|b t] //=; rewrite IH. Qed.

Fixpoint zip_with_index_from {A} {B} {C} `{Num B} (z : B) (f : A → B → C) (s : list A) : list C :=
  match s with
    | [::]    => [::]
    | a :: s' => f a z :: zip_with_index_from (z + #1) f s'
  end.

Definition zip_with_index {A} {B} {C} `{Num B} : (A → B → C) → list A → list C :=
  zip_with_index_from #0.

Theorem zip_with_index_from_is_zip_with {A} {B} (z : nat) (f : A → nat → B) (s : list A) :
  zip_with_index_from z f s = zip_with f s (indices_from z s).
Proof. by elim: s z => [|a s IH] z //=; rewrite /BinPos.Pos.to_nat /= addn1 IH. Qed.

Theorem zip_with_index_is_zip_with {A} {B} (f : A → nat → B) (s : list A) :
  zip_with_index f s = zip_with f s (indices s).
Proof. by rewrite -zip_with_index_from_is_zip_with. Qed.

Notation "[ 'seq' E | i ← s | j ← t ]"     := (zip_with       (fun i j => E) s t)
  (at level 0, E at level 99, i ident, j ident,
   format "[ '[hv' 'seq'  E '/ '  |  i  ←  s '/ '  |  j  ←  t ] ']'").
Notation "[ 'seq' E | i ← s | j 'index' ]" := (zip_with_index (fun i j => E) s)
  (at level 0, E at level 99, i ident, j ident,
   format "[ '[hv' 'seq'  E '/ '  |  i  ←  s '/ '  |  j  'index' ] ']'").

Notation "[ 'seq' E | i <- s | j <- t ]"    := [seq E | i ← s | j ← t]
  (at level 0, E at level 99, i ident, j ident, only parsing).
Notation "[ 'seq' E | i <- s | j 'index' ]" := [seq E | i ← s | j index]
  (at level 0, E at level 99, i ident, j ident, only parsing).

Notation "[ 'seq' E | i ← s ]" := [seq E | i <- s]
  (at level 0, E at level 99, i ident,
   format "[ '[hv' 'seq'  E '/ '  |  i  ←  s ] ']'").
Notation "[ 'seq' E | i : T ← s ]" := [seq E | i : T <- s]
  (at level 0, E at level 99, i ident, only parsing).

Fixpoint unzip {A} {B} (s : list (A * B)) : list A * list B :=
  match s with
    | [::]        => ([::], [::])
    | (a,b) :: s' => let: (sa,sb) := unzip s'
                     in (a::sa, b::sb)
  end.

Theorem unzip_is_unzips {A} {B} (s : list (A * B)) :
  unzip s = (unzip1 s, unzip2 s).
Proof. by elim: s => [|[a b] s IH] //=; rewrite IH. Qed.

(******************************************************************************)

Inductive Context := EmptyCtx
                   | AddCtx : ∀ (Σ : Context) (n : Var) (e : CoreExpr), Context.

Notation "·" := EmptyCtx.
Notation "Σ &[ n ↦ e ]" := (AddCtx Σ n e) (at level 50, format "Σ  &[ n  ↦  e ]").

Definition addManyCtx (Σ : Context) (ns : list Var) (es : list CoreExpr) : Context :=
  foldl (fun Σ' ne => Σ' &[ne.1 ↦ ne.2]) Σ (zip ns es).

Notation "Σ &*[ ns ↦* es ]" := (addManyCtx Σ ns es)
  (at level 50, format "Σ  &*[ ns  ↦*  es ]").

Axiom lookup : Context → Var → option CoreExpr. (* Requires some sort of comparison *)

Axiom subst       : CoreExpr → Var      → CoreExpr      → CoreExpr. (* Presumably convertable *)
Axiom multisubst  : CoreExpr → list Var → list CoreExpr → CoreExpr. (* Presumably convertable *)
Axiom multisubst' : CoreExpr → list (Var * CoreExpr)    → CoreExpr. (* Presumably convertable *)
Notation "e₁ $[ n ↦ e₂ ]" := (subst e₁ n e₂)
  (at level 50, format "e₁ $[ n ↦ e₂ ]", left associativity).
Notation "e $*[ ns ↦* es' ]" := (multisubst e ns es')
  (at level 50, format "e $*[ ns ↦* es' ]", left associativity).
Notation "e' $*[*↦*] nes" := (multisubst' e' nes)
  (at level 50, left associativity).

Axiom fv : CoreExpr → VarSet. (* Convertable, but maybe not at this type. *)

Axiom mkVarSet : list Var → VarSet. (* Convertable *)
Axiom isEmptyVarSet : VarSet → bool. (* Convertable *)
Axiom intersectVarSet : VarSet → VarSet → VarSet. (* Convertable *)
Infix "∩ᵥ" := intersectVarSet (at level 40).

Axiom isDataConId_maybe : Id → option DataCon. (* Convertable *)

Axiom coercionKind     : Coercion → Pair Type_. (* Converted *)
Axiom dataConRepType   : DataCon → Type_.       (* Converted *)
Axiom mkForAllTys      : list TyBinder -> Type_ -> Type_. (* Convertable *)
Axiom partitionBinders : list TyBinder -> (list TyVar * list Type_). (* Convertable *)

(******************************************************************************)

Notation "e ▷ γ" := (Mk_Cast e γ) (at level 40, left associativity).

Notation "'ƛ' n ',' e" := (Mk_Lam n e) (at level 200, left associativity, format "ƛ n ,  e").

Infix "@@" := Mk_App (at level 20, left associativity).

(* From the converter, prettified *)
Arguments Mk_App {_} _ _.
Definition mkApps {b} (f : Expr b) (args : list (Arg b)) : Expr b :=
  foldl Mk_App f args.
Infix "@@*" := mkApps (at level 20, left associativity).

Notation "⟨ τ ⟩ᴺ" := (Mk_Refl Mk_Nominal          τ) (format "⟨ τ ⟩ᴺ").
Notation "⟨ τ ⟩ᴿ" := (Mk_Refl Mk_Representational τ) (format "⟨ τ ⟩ᴿ").
Notation "⟨ τ ⟩ᴾ" := (Mk_Refl Mk_Phantom          τ) (format "⟨ τ ⟩ᴾ").

(* (do-add-in-font ?\⨾ (font-spec :name "Apple Symbols" :size 14)) *)
Infix "⨾" := Mk_TransCo (at level 40).

Infix "@!" := Mk_AppCo (at level 20, left associativity).

(******************************************************************************)

Reserved Notation "Σ '[op]⊢' e ⟶ e'" (at level 99).
Inductive SingleStep (Σ : Context) : CoreExpr → CoreExpr → Type :=

  | S_Var : ∀ n e,
      lookup Σ n = Some e
      →
      Σ [op]⊢ Mk_Var n ⟶ e
  
  | S_App : ∀ e₁ e₁' e₂,
      Σ [op]⊢ e₁ ⟶ e₁'
      →
      Σ [op]⊢ e₁ @@ e₂ ⟶ e₁' @@ e₂

  | S_Beta : ∀ n e₁ e₂,
      Σ [op]⊢ (ƛ n, e₁) @@ e₂ ⟶ e₁$[n ↦ e₂]
  (* TODO: Evaluate under *type* lambdas *)

  | S_Push : ∀ n e₁ γ e₂,
      let γ₀ := Mk_SymCo (Mk_NthCo #0 γ) in
      let γ₁ := Mk_NthCo #1 γ in
      (∄ τ, e₂ = Mk_Type τ) →
      (∄ γ, e₂ = Mk_Coercion γ)
      →
      Σ [op]⊢ ((ƛ n, e₁) ▷ γ) @@ e₂ ⟶ (ƛ n, e₁ ▷ γ₁) @@ (e₂ ▷ γ₀)

  | S_TPush : ∀ n e γ τ,
      Σ [op]⊢ ((ƛ n, e) ▷ γ) @@ Mk_Type τ ⟶ (ƛ n, e ▷ (γ @! Mk_CoVarCo n)) @@ Mk_Type τ

  | S_CPush : ∀ n e γ γ',
      let γ₀ := Mk_NthCo #1 (Mk_NthCo #0 γ) in
      let γ₁ := Mk_SymCo (Mk_NthCo #2 (Mk_NthCo #0 γ)) in
      let γ₂ := Mk_NthCo #1 γ
      in
      Σ [op]⊢ ((ƛ n, e) ▷ γ) @@ Mk_Coercion γ' ⟶ (ƛ n, e ▷ γ₂) @@ Mk_Coercion (γ₀ ⨾ γ' ⨾ γ₁)
  
  (* For determinism, may want to require `e` to be a value *)
  | S_Trans : ∀ e γ₁ γ₂,
      Σ [op]⊢ (e ▷ γ₁) ▷ γ₂ ⟶ e ▷ (γ₁ ⨾ γ₂)

  | S_Cast : ∀ e γ e',
      Σ [op]⊢ e ⟶ e'
      →
      Σ [op]⊢ e ▷ γ ⟶ e' ▷ γ
        
  (* Or: `Mk_Tick tick e ⟶ e` *)
  | S_Tick : ∀ tick e e',
      Σ [op]⊢ e ⟶ e'
      →
      Σ [op]⊢ Mk_Tick tick e ⟶ Mk_Tick tick e'

  | S_Case : ∀ e n τ alts e',
      Σ [op]⊢ e ⟶ e'
      →
      Σ [op]⊢ Mk_Case e n τ alts ⟶ Mk_Case e' n τ alts
  
  (* In the source, we have "u' := u[n ↦ e]…"; I believe "e" should actually be
     the matched term. *)
  | S_MatchData : ∀ K K_con τs' σs es n τ alts αs xs u,
      isDataConId_maybe K = Some K_con →
      length αs = length σs →
      length xs = length es →
      (Mk_DataAlt K_con, αs ++ xs, u) ∈ alts →
      let u' := u$[n ↦ Mk_Var K @@* τs' @@* σs @@* es]$*[αs ↦* σs]$*[xs ↦* es]
      in
      Σ [op]⊢ Mk_Case (Mk_Var K @@* τs' @@* σs @@* es) n τ alts ⟶ u'

  | S_MatchLit : ∀ lit n τ alts u,
      (Mk_LitAlt lit, [::], u) ∈ alts
      →
      Σ [op]⊢ Mk_Case (Mk_Lit lit) n τ alts ⟶ u$[n ↦ Mk_Lit lit]

  | S_MatchDefault : ∀ e n τ alts u,
      (Mk_DEFAULT, [::], u) ∈ alts →
      (* Factor out from S_MatchData? *)
      [\/ ∃ K K_con τs' σs es,
            isDataConId_maybe K = Some K_con ∧
            e = (Mk_Var K @@* τs' @@* σs @@* es) ∧
            ∄ αs xs u,
              length αs = length σs ∧
              length xs = length es ∧
              (Mk_DataAlt K_con, αs ++ xs, u) ∈ alts
      (* Factor out from S_MatchLit? *)
      |   ∃ lit,
            e = Mk_Lit lit ∧
            ∄ u,
              (Mk_LitAlt lit, [::], u) ∈ alts ]
      →
      Σ [op]⊢ Mk_Case e n τ alts ⟶ u$[n ↦ e]

(* Just use `Mk_InstCo`! *)
(* Can't do the tricky `liftCoSubst` case – the `$*[*↦*]`s below are lies. *)
(*
  | S_CasePush : ∀ K τs σs es γ n τ₂ alts T τs' αs αs_vars βs βs_vars τs₁,
      partitionBinders αs = (αs_vars, [::]) →
      partitionBinders βs = (βs_vars, [::]) →
      length τs  = length τs' →
      length τs  = length αs  →
      length σs  = length βs  →
      length τs₁ = length es  →
      Mk_Pair (Mk_TyConApp T τs) (Mk_TyConApp T τs') = coercionKind γ →
      mkForAllTys αs (mkForAllTys βs
        (mkForAllTys (map Mk_Anon τs₁) (Mk_TyConApp T (map Mk_TyVarTy αs_vars))))
          = dataConRepType K →
      let es' := [seq
                    e ▷ (τ₁ $*[*↦*] [seq (α, Mk_NthCo a γ) | α ← αs_vars | a index]
                            $*[*↦*] [seq (β, ⟨σ⟩ᴺ)         | β ← βs_vars | σ ← σs])
                 | e ← es | τ₁ ← τs₁]
      in
      Σ [op]⊢ Mk_Case (K @@* τs @@* σs @@* es ▷ γ) n τ₂ alts ⟶
                Mk_Case (K @@* τs' @@* σs @@* es') n τ₂ alts
*)

  | S_LetNonRec : ∀ n e₁ e₂,
      Σ [op]⊢ Mk_Let (Mk_NonRec n e₁) e₂ ⟶ e₂$[n ↦ e₁]

  | S_LetRec : ∀ ns es u u',
      length ns = length es →
      Σ &*[ns ↦* es] [op]⊢ u ⟶ u'
      →
      Σ [op]⊢ Mk_Let (Mk_Rec (zip ns es)) u ⟶ Mk_Let (Mk_Rec (zip ns es)) u'

  | S_LetRecApp : ∀ ns es u e',
      length ns = length es
      →
      Σ [op]⊢ Mk_Let (Mk_Rec (zip ns es)) u @@ e' ⟶ Mk_Let (Mk_Rec (zip ns es)) (u @@ e')

  | S_LetRecCast : ∀ ns es u γ,
      length ns = length es
      →
      Σ [op]⊢ Mk_Let (Mk_Rec (zip ns es)) u ▷ γ ⟶ Mk_Let (Mk_Rec (zip ns es)) (u ▷ γ)

  | S_LetRecCase : ∀ ns es u n₀ τ alts,
      length ns = length es
      →
      Σ [op]⊢ Mk_Case (Mk_Let (Mk_Rec (zip ns es)) u) n₀ τ alts ⟶
                Mk_Let (Mk_Rec (zip ns es)) (Mk_Case u n₀ τ alts)

  | S_LetRecFlat : ∀ ns es ns' es' u,
      length ns  = length es →
      length ns' = length es'
      →
      Σ [op]⊢ Mk_Let (Mk_Rec (zip ns es)) (Mk_Let (Mk_Rec (zip ns' es')) u) ⟶
                Mk_Let (Mk_Rec (zip (ns ++ ns') (es ++ es'))) u

  | S_LetRecReturn : ∀ ns es u,
      length ns = length es →
      isEmptyVarSet (fv u ∩ᵥ mkVarSet ns)
      →
      Σ [op]⊢ Mk_Let (Mk_Rec (zip ns es)) u ⟶ u

where "Σ '[op]⊢' e ⟶ e'" := (SingleStep Σ e e').
