Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Mon Require Import SPropBase.

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl Package Prelude
  SigmaProtocol.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.
Set Equations Transparent.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.


Import GroupScope GRing.Theory.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

Import PackageNotation.

From NominalSSP Require Import FsetSolve Group Nominal NomPackage Disjoint Sigma Prelude.

Module Commitment. 
Local Open Scope ring_scope.


Record raw_nomCom := 
 { p :> raw_sigma ;
  sampl_wit : code fset0 [interface] (Witness p) ;
  sampl_challenge : code fset0 [interface] (Challenge p) ;
  key_gen : (Witness p ) → (Statement p)
 }.



  Definition INIT : nat := 2.
  Definition GET : nat := 3.



Definition setup_loc : Location := ('bool; 10%N).
Definition statement_loc (p: raw_nomCom) : Location := ('statement  p; 11%N).
Definition witness_loc (p: raw_nomCom) : Location := ('witness p; 12%N).
Definition KEY_locs (p: raw_nomCom) : {fset Location} := fset [:: setup_loc; witness_loc p ; statement_loc p].


Notation " 'open p " := (chOpening p) (in custom pack_type at level 2, p constr).
(* Notation " 'chKeys p " := (chProd ('statement p) ('witness p)) 
                            (in custom pack_type at level 2, p constr).
Parameter KeyGen : ∀ (p: raw_sigma) (w : 'witness p) , 'statement p.
 *)

Notation Key_E p := [interface
                       #val #[ INIT ] : 'unit → 'unit ;
                       #val #[ GET ] : 'unit → ('statement p)
                    ].


     Definition KEY (p: raw_nomCom):
      game (Key_E p)
      :=
      [module (KEY_locs p) ;
         #def #[ INIT ] (_ : 'unit) : 'unit {
           b ← get setup_loc ;;
           #assert (negb b) ;;
           w ← p.(sampl_wit) ;;
           let h := p.(key_gen) w in
           #assert p.(R) h w ;;
           #put setup_loc := true ;;
           #put statement_loc p := h ;;
           #put witness_loc p := w ;;
           @ret 'unit Datatypes.tt
         }
         ;
         #def #[ GET ] (_ : 'unit) : ('statement p) {
           b ← get setup_loc ;;
           if b then
             h ← get (statement_loc p) ;;
             ret h
           else
             fail
         }
      ].



Definition COM : nat := 5.
Definition OPEN : nat := 6.
Definition VER : nat := 7.


Definition challenge_loc (p: raw_nomCom) : Location := ('option ('challenge p); 13%N).
Definition response_loc (p: raw_nomCom) : Location := ('option ('response p); 14%N).
Definition Com_locs (p: raw_nomCom) : {fset Location} := fset [:: challenge_loc p; response_loc p].

Definition Com_E p := [interface
                        #val #[ COM ] : ('challenge p) → ('message p) ;
                        #val #[ OPEN ] : 'unit → ('open p) ;
                        #val #[ VER ] : ('transcript p) → 'bool
                      ].

    Definition Sigma_to_Com (p: raw_nomCom):
      module (Key_E p) (Com_E p)
      := 
      [module (Com_locs p) ;
        #def #[ COM ] ('(e) : 'challenge p) : ('message p)
        {
          #import {sig #[ INIT ] : 'unit → 'unit } as key_gen_init ;;
          #import {sig #[ GET ] : 'unit → ('statement p) } as key_gen_get ;;
          _ ← key_gen_init Datatypes.tt ;;
          h ← key_gen_get Datatypes.tt ;;
          '(a, z) ← p.(simulate) h e ;;
          #put challenge_loc p := Some e ;;
          #put response_loc p := Some z ;;
          @ret ('message p) a
        }
        ; 
        #def #[ OPEN ] (_ : 'unit) : ('open p)
        {
          o_e ← get (challenge_loc p) ;;
          o_z ← get (response_loc p) ;;
          match (o_e, o_z) with
          | (Some e, Some z) => @ret (chOpening p) (e, z)
          | _ => fail
          end
        }
        ;
        #def #[ VER ] ('(h,a,e,z) : 'transcript p) : 'bool (* Er denne signatur nødvendig, siden p allerede har verify *)
        {
          @ret 'bool (p.(verify) h a e z)
        }
      ].


    #[tactic=notac] Equations? Sigma_to_Com_Aux (p: raw_nomCom):
      module (Transcript p) (Com_E p)
      := Sigma_to_Com_Aux p := 
      [ module (setup_loc |: Com_locs p) ;
        #def #[ COM ] ('(e) : 'challenge p) : ('message p)
        {
          #import {sig #[ TRANSCRIPT ] : ('input p) → ('transcript p) } as RUN ;;
          b ← get setup_loc ;;
          #assert (negb b) ;;
          w ← p.(sampl_wit) ;;
          let h := p.(key_gen) w in
          #assert p.(R) h w ;;
          #put setup_loc := true ;;
          '(h, a, e, z) ← RUN (h, w, e) ;;
          #put challenge_loc p := Some e ;;
          #put response_loc p := Some z ;;
          @ret ('message p) a
        }
       ;
        #def #[ OPEN ] (_ : 'unit) : ('open p)
        {
          o_e ← get (challenge_loc p) ;;
          o_z ← get (response_loc p) ;;
          match (o_e, o_z) with
          | (Some e, Some z) => @ret (chOpening p) (e, z)
          | _ => fail
          end
        }
        ;
        #def #[ VER ] ('(h,a,e,z) : 'transcript p) : 'bool
        {
          @ret 'bool (p.(verify) h a e z)
        }
      ].
    Proof.
      unfold Com_locs.
      ssprove_valid.
    Qed.


Definition HIDING : nat := 8.


Definition Hiding_E p := [interface #val #[ HIDING ] : ('challenge p) → ('message p) ].


    (* Commitment to input value*)
    Definition Hiding_real (p: raw_nomCom) :
      module (Com_E p) (Hiding_E p)
      :=
      [module no_locs ;
        #def #[ HIDING ] ('(e) : 'challenge p) : ('message p)
        {
          #import {sig #[ COM ] : ('challenge p) → ('message p) } as com ;;
          a ← com e ;;
          @ret ('message p) a
        }
      ].

    (* Commitment to random value *)
    Definition Hiding_ideal (p: raw_nomCom) :
      module (Com_E p) (Hiding_E p)
      :=
      [module no_locs ;
        #def #[ HIDING ] (_ : 'challenge p) : ('message p)
        {
          #import {sig #[ COM ] : ('challenge p) → ('message p) } as com ;;
          e ← p.(sampl_challenge) ;;
          t ← com e ;;
          @ret ('message p) t

        }
      ].


    Definition ɛ_hiding A (p: raw_nomCom) :=
      Adv
        (Hiding_real p ∘ Sigma_to_Com p ∘ KEY p)
        (Hiding_ideal p ∘ Sigma_to_Com p ∘ KEY p) 
        (A ∘ (KEY p || (ID (Hiding_E p)))). 

    (* lemma nedenfor taget fra schnorr. *)
(*     Lemma heap_ignore_locs (p: raw_nomCom) :
      Invariant (locs p) fset0 (heap_ignore (locs p)).
    Proof. ssprove_invariant. apply fsubsetUl. Qed. *)



Fixpoint Adv_sum P l Q A :=
  match l with
  | [::] => Adv P Q A
  | R :: l => Adv_sum P l R A + Adv R Q A
  end.

Lemma AdvantageD_sum_chain {P Q A} l : Adv P Q A <= Adv_sum P l Q A.
  move: Q. induction l => //= Q.
  advantage_trans a. 
  by apply lerD.
Qed.

Ltac nssprove_triangle l :=
  eapply le_trans; [ apply (AdvantageD_sum_chain (rev l))| unfold AdvantageD_sum].



    Theorem commitment_hiding (p: raw_nomCom) :
      ∀ (A: nom_package),
        ValidPackage (loc A) 
          (Hiding_E p)
          A_export (A ∘ (KEY p || ID (Hiding_E p))) → 
          (ɛ_hiding A p) <= 
           0
           + AdvantageD (SHVZK_ideal p) 
                        (SHVZK_real p) 
                        (A ∘ (KEY p || ID (Hiding_E p)) ∘ Hiding_real p ∘ Sigma_to_Com_Aux p)
           + AdvantageD (Hiding_real p ∘ Sigma_to_Com_Aux p ∘ SHVZK_real p) 
                        (Hiding_ideal p ∘ Sigma_to_Com_Aux p ∘ SHVZK_real p) 
                        (A ∘ (KEY p || ID (Hiding_E p)))
           + AdvantageD (SHVZK_real p) 
                        (SHVZK_ideal p) 
                        (A ∘ (KEY p || ID (Hiding_E p)) ∘ Hiding_ideal p ∘ Sigma_to_Com_Aux p)
           + 0.
    Proof.
      unfold ɛ_hiding. intros.
      nssprove_triangle [::
        (Hiding_real p ⊛ Sigma_to_Com_Aux p ⊛ SHVZK_ideal p) ;
        (Hiding_real p ⊛ Sigma_to_Com_Aux p ⊛ SHVZK_real p) ;
        (Hiding_ideal p ⊛ Sigma_to_Com_Aux p ⊛ SHVZK_real p) ;
        (Hiding_ideal p ⊛ Sigma_to_Com_Aux p ⊛ SHVZK_ideal p)
        ]. 
      simpl.
      repeat apply lerD.
      2: { rewrite 2!AdvantageD_dlink 2!dlink_assoc //. }
      2: { done. }
      2: { rewrite 2!AdvantageD_dlink 2!dlink_assoc //. }
      - apply eq_ler. eapply AdvantageD_perf. Search AdvantageD.
        2: {apply H.
          1: {






