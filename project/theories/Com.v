
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

From NominalSSP Require Import FsetSolve Group SSProve Nominal NomPackage Disjoint Prelude Sigma Reductions.
Import Num.Def Num.Theory Order.POrderTheory.
Import PackageNotation.

#[local] Open Scope ring_scope.

Record raw_com := 
  { Key : choice_type
  ; Value : choice_type
  ; Commitment : choice_type 
  ; Opening : choice_type

  ; setup : 
      code no_locs [interface] Key

  ; commit :
    ∀ (k : Key) (u : Value),
      code no_locs [interface] (Commitment × Opening)

  ; verify :
    ∀ (k : Key) (c : Commitment) (v: Value) (d : Opening),
      code no_locs [interface] bool

  ; sampl_value : 
      code no_locs [interface] Value

  }.


#[local] Open Scope package_scope.


Notation " 'key p " := (Key p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'value p " := (Value p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'commitment p " := (Commitment p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'opening p " := (Opening p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'key p " := (Key p)
  (at level 3) : package_scope.

Notation " 'value p " := (Value p)
  (at level 3) : package_scope.

Notation " 'commitment p " := (Commitment p)
  (at level 3) : package_scope.

Notation " 'opening p " := (Opening p)
  (at level 3) : package_scope.



(* ---- Correctnes ---- *)

Definition CORRECTNESS := 5%N.

Definition ICorrect_com p := [interface #val #[ CORRECTNESS ] : ('value p) → ('bool) ].

    Definition Correct_real p : 
        game (ICorrect_com p) :=
        [module no_locs ;
           #def #[ CORRECTNESS ] (v : 'value p) : ('bool) 
            {
              k ← p.(setup) ;;
              '(c, o) ← p.(commit) k v ;;
              b ← p.(verify) k c v o ;;
              ret b

            }
        ].


    Definition Correct_ideal p : 
        game (ICorrect_com p) :=
        [module no_locs ;
           #def #[ CORRECTNESS ] (v : 'value p) : ('bool) 
            {
              k ← p.(setup) ;;
              ret true
            }
        ].

Definition Correct p b :=
  if b then Correct_real p else Correct_ideal p.


Definition Adv_Correct p (ε : adversary (ICorrect_com p) → Axioms.R) :=
  ∀ A : adversary (ICorrect_com p), AdvFor (Correct p) A <= ε A.



(* ---- Hiding ---- *) 

Definition COMMITMENT := 2%N.

Definition ICommitment p := [interface #val #[ COMMITMENT ] : ('value p) → 'commitment p ].

    Definition Hiding_real p : 
        game (ICommitment p) := 
        [module no_locs ;
           #def #[ COMMITMENT ] (v : 'value p) : ('commitment p)
            {
              k ← p.(setup) ;;
              _ ← p.(sampl_value) ;;
              '(c, o) ← p.(commit) k v ;;
              @ret ('commitment p) c 
            }
        ].

    Definition Hiding_ideal p : 
        game (ICommitment p) := 
        [module no_locs ; 
           #def #[ COMMITMENT ] (v : 'value p) : ('commitment p)
            {
              k ← p.(setup) ;;
              u ← p.(sampl_value) ;;
              '(c, o) ← p.(commit) k u ;;           
              @ret ('commitment p) c 
            }
        ].


Definition Hiding p b :=
  if b then Hiding_real p else Hiding_ideal p.


Definition Adv_Hiding p (ε : adversary (ICommitment p) → Axioms.R) :=
  ∀ A : adversary (ICommitment p), AdvFor (Hiding p) A <= ε A.



(* ---- Binding ---- *) 

Definition chBinding p := 'key p × 'commitment p × 'value p × 'opening p × 'value p × 'opening p.

Notation " 'binding p " := (chBinding p) (in custom pack_type at level 2, p constr).

Definition BINDING := 3%N.

Definition IBinding p := [interface #val #[ BINDING ] : ('binding p) → 'bool ].


    Definition Binding_real p : 
        game (IBinding p) := 
        [module no_locs ;
            #def #[ BINDING ] ('(k, c, v, o, v', o') : 'binding p) : 'bool
            { 
              b ← p.(verify) k c v o ;;
              b' ← p.(verify) k c v' o' ;; 
              #assert b ;;
              #assert b' ;;
              #assert (v != v') ;;
              @ret 'bool true

            }
        ].

    Definition Binding_ideal p :
         game (IBinding p) := 
        [module no_locs ;
            #def #[ BINDING ] ('(k, c, v, o, v', o') : 'binding p) : 'bool
            {
              p.(verify) k c v o ;;
              p.(verify) k c v' o' ;; 
              @ret 'bool false
            }
        ].

Definition Binding p b :=
  if b then Binding_real p else Binding_ideal p.


Definition Adv_Binding p (ε : adversary (IBinding p) → Axioms.R) :=
  ∀ A : adversary (IBinding p), AdvFor (Binding p) A <= ε A.


(* ------------------------------------- *)
(* Commitment Scheme from Sigma Protocol *)
(* ------------------------------------- *)


Record raw_sigExt := 
  { p :> raw_sigma 
  ; sampl_wit : 
      code no_locs [interface] (Witness p) 

  ; sampl_challenge : 
      code no_locs [interface] (Challenge p) 

  ; key_gen :  ∀ (w : Witness p),
      code no_locs [interface] (Statement p)
  }.


Definition sig_to_com (p : raw_sigExt) : raw_com :=
  {| Key := p.(Statement)
   ; Value := p.(Challenge) 
   ; Commitment := p.(Message) 
   ; Opening := p.(Response)
 
   ; setup := 
     {code 
       w ← p.(sampl_wit) ;; 
       h ← (p.(key_gen) w) ;;
       #assert p.(R) h w ;;
       ret ((h) : _)
      }

   ; commit := λ k u,
     {code
       '(a, z) ← p.(simulate) k u ;;
       ret ((a, z) : (_ × _))
     }

   ; verify := λ k c v d,
     {code 
        ret (p.(Sigma.verify) k c v d)%B
     }

   ; sampl_value := p.(sampl_challenge)

  |}.


(* ---- CORRECTNESS RELATED TO COMPLETENESS ---- *)

(* Reduction module from Correctness of commitment scheme to Correctness of sigma *)

Definition Call_correct_sig (p: raw_sigExt) :
  module (ICorrect p) (ICorrect_com (sig_to_com p)) := 
  [module no_locs ;
      #def #[ CORRECTNESS ] (v : 'value (sig_to_com p)) : 'bool
          {
            #import {sig #[ RUN ] : ('input p) → 'bool} as COR ;;
            w ← p.(sampl_wit) ;; 
            h ← p.(key_gen) w ;;
            #assert p.(R) h w ;;
            b ← COR (h, w, v) ;;
            ret b
          }
  ].

Lemma Correct_ideal_sim_perf p :
  perfect (ICorrect_com (sig_to_com p))
    (Call_correct_sig p ∘ Sigma.Correct_ideal p) (Correct_ideal (sig_to_com p)).
Proof.
    nssprove_share.
    eapply prove_perfect.
    eapply eq_rel_perf_ind_eq.
    simplify_eq_rel e.
    ssprove_code_simpl; rewrite cast_fun_K.
    apply rsame_head => w.
    apply rsame_head => h.
    ssprove_code_simpl_more.
    ssprove_sync_eq => H.
    rewrite H //=.
    apply r_ret. auto.
Qed.

Lemma Correct_real_sim_perf p :
   perfect (ICorrect_com (sig_to_com p)) 
    (Call_correct_sig p ∘ Correct_sim p) (Correct_real (sig_to_com p)).
Proof.
    unfold Correct_sim.
    rewrite sep_link_assoc.
    nssprove_share.
    rewrite -share_link_assoc.
    rewrite move0.
    -   eapply prove_perfect.
        apply eq_rel_perf_ind_eq.
        simplify_eq_rel e. 
        do 2 (ssprove_code_simpl; rewrite cast_fun_K).
        apply rsame_head => w.
        apply rsame_head => h.
        ssprove_code_simpl_more.
        ssprove_sync_eq => H.
        rewrite H //=.
        ssprove_code_simpl.
        apply rsame_head => sim.
        destruct sim.
        apply r_ret. auto.
    - Admitted.
 

Theorem Com_Correct_Correct:
  ∀ (p : raw_sigExt) ,
  Adv_Correct (sig_to_com p) (λ A,
    AdvFor (SHVZK p) (A ∘ Call_correct_sig p ∘ Verify_call p) + AdvFor (Sigma.Correct p) (A ∘ Call_correct_sig p)).
Proof.
  intros p A.
  nssprove_adv_trans (Call_correct_sig p ∘ Correct_sim p)%sep.
  simpl. rewrite Adv_sym. rewrite Correct_real_sim_perf.
  rewrite GRing.add0r.
  nssprove_adv_trans (Call_correct_sig p ∘ Sigma.Correct_ideal p)%sep.
  rewrite Correct_ideal_sim_perf. rewrite GRing.addr0.
  rewrite Adv_sep_link. rewrite /AdvFor (sep_link_assoc A).
  apply (Adv_Correct_sim p {adversary (ICorrect p) ; A ∘ Call_correct_sig p}).
Qed.



(* ---- HIDING RELATED TO SHVZK ---- *)

(* Reduction module with input *)

Definition Call_SHVZK_inp (p: raw_sigExt) :
  module (Transcript p) (ICommitment (sig_to_com p)) := 
  [module no_locs ;
      #def #[ COMMITMENT ] (v : 'value (sig_to_com p)) : ('commitment (sig_to_com p))
          {
            #import {sig #[ TRANSCRIPT ] : ('input p) → 'transcript p} as TRANS ;;
            w ← p.(sampl_wit) ;; 
            h ← p.(key_gen) w ;;
            #assert p.(R) h w ;;
            _ ← (sig_to_com p).(sampl_value) ;;
            '(h, a, e, z) ← TRANS (h, w, v) ;;           
            ret (a : (sig_to_com p).(Commitment))  
            
          }
  ].

(* Reduction module with sampling *)

Definition Call_SHVZK_sam (p: raw_sigExt) :
  module (Transcript p) (ICommitment (sig_to_com p)) := 
  [module no_locs ;
      #def #[ COMMITMENT ] (v : 'value (sig_to_com p)) : ('commitment (sig_to_com p))
          {
            #import {sig #[ TRANSCRIPT ] : ('input p) → 'transcript p} as TRANS ;;
            w ← p.(sampl_wit) ;; 
            h ← p.(key_gen) w ;;
            #assert p.(R) h w ;;
            u ← (sig_to_com p).(sampl_value) ;;
            '(h, a, e, z) ← TRANS (h, w, u) ;;           
            ret (a : (sig_to_com p).(Commitment))  
            
          }
  ].


(* Hiding_real and SHVZK_ideal perf ind. *)

Lemma Hiding_real_SHVZK_ideal_perf p : 
  perfect (ICommitment (sig_to_com p)) 
    (Hiding_real (sig_to_com p)) (Call_SHVZK_inp p ∘ SHVZK_ideal p).
Proof.
    nssprove_share.
    eapply prove_perfect.
    eapply eq_rel_perf_ind_eq.
    simplify_eq_rel e.
    ssprove_code_simpl; rewrite cast_fun_K.
    apply rsame_head => w.
    apply rsame_head => h.
    ssprove_code_simpl_more.
    ssprove_sync_eq => H.
    apply rsame_head => sampl.
    ssprove_code_simpl_more.
    rewrite H //=.
    ssprove_code_simpl.
    apply rsame_head => sim.
    destruct sim.
    apply r_ret. auto.
Qed.


(* Hiding_ideal and SHVZK_ideal perf ind. *)


Lemma Hiding_ideal_SHVZK_ideal_perf p : 
  perfect (ICommitment (sig_to_com p)) 
    (Call_SHVZK_sam p ∘ SHVZK_ideal p) (Hiding_ideal (sig_to_com p)).
Proof.
    nssprove_share.
    eapply prove_perfect.
    eapply eq_rel_perf_ind_eq.
    simplify_eq_rel e.
    ssprove_code_simpl; rewrite cast_fun_K.
    apply rsame_head => w.
    apply rsame_head => h.
    ssprove_code_simpl_more.
    ssprove_sync_eq => H.
    apply rsame_head => sampl.
    ssprove_code_simpl_more.
    rewrite H //=.
    ssprove_code_simpl.
    apply rsame_head => sim.
    destruct sim.
    apply r_ret. auto.
Qed.



Lemma Red_perf (p: raw_sigExt) :
  (forall h w a s e, NoFail (response p h w a s e)) -> 
  perfect (ICommitment (sig_to_com p)) 
      (Call_SHVZK_inp p ∘ SHVZK_real p) (Call_SHVZK_sam p ∘ SHVZK_real p).
Proof.
    intros.
    do 2 nssprove_share.
    eapply prove_perfect.
    eapply eq_rel_perf_ind_eq.
    simplify_eq_rel e'.
    ssprove_code_simpl; rewrite cast_fun_K.
    ssprove_code_simpl.
    apply rsame_head => w'.
    apply rsame_head => h'.
    ssprove_sync_eq => H1.
    apply rsame_head => sampl.
    ssprove_code_simpl_more.
    ssprove_sync_eq => _.
    ssprove_code_simpl. 
    apply rsame_head => a'.
    destruct a'.
    eapply r_NoFail_L.
    - apply H.
    - intros z1. apply r_NoFail_R.
      + apply H.
      + intros z2. apply r_ret. auto.
Qed.


(* Hiding Theorem *)

Theorem Com_hiding_SHVZK :
  ∀ (p : raw_sigExt) ,
  (forall h w a s e, NoFail (response p h w a s e)) ->
  Adv_Hiding (sig_to_com p) (λ A,
    AdvFor (SHVZK p) (A ∘ Call_SHVZK_inp p) +
    AdvFor (SHVZK p) (A ∘ Call_SHVZK_sam p)).

Proof.
  intros p H A.
  nssprove_adv_trans (Call_SHVZK_inp p ∘ SHVZK_ideal p)%sep.
  rewrite Hiding_real_SHVZK_ideal_perf.
  rewrite GRing.add0r.
  nssprove_adv_trans (Call_SHVZK_sam p ∘ SHVZK_ideal p)%sep.
  rewrite Hiding_ideal_SHVZK_ideal_perf.
  rewrite GRing.addr0.
  nssprove_adv_trans (Call_SHVZK_sam p ∘ SHVZK_real p)%sep.
  apply lerD.
  - nssprove_adv_trans (Call_SHVZK_inp p ∘ SHVZK_real p)%sep.
    rewrite Red_perf.
    + rewrite GRing.addr0.
      rewrite Adv_sep_link Adv_sym.
      apply le_refl.
    + apply H.
  - rewrite Adv_sep_link.
    apply le_refl.
Qed.



(* ---- BINDING RELATED TO SOUNDNESS ---- *)

Definition Call_Soundness (p: raw_sigExt) :

  module (Soundness p) (IBinding (sig_to_com p)) := 
  [module no_locs ;
      #def #[ BINDING ] ('(k, c, v, o, v', o') : 'binding (sig_to_com p)) : 'bool
          {
            #import {sig #[ SOUNDNESS ] : ('soundness p) → 'bool} as SOUND ;;
            'b ← SOUND ((k, c), ((v, o), (v', o'))) ;;
            ret b
          }
  ].


(* Binding Theorem *)

Theorem Com_Binding_Soundness p :
  perfect (IBinding (sig_to_com p))
   (Binding_real (sig_to_com p)) (Call_Soundness p ∘ Special_Soundness_t p).
Proof.
  nssprove_share.
  eapply prove_perfect.
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel e.
  ssprove_code_simpl; rewrite cast_fun_K.
  destruct e as [[[[[k c] v] o] v'] o'].
  ssprove_code_simpl_more.
  ssprove_sync_eq => H1.
  ssprove_sync_eq => H2.
  ssprove_sync_eq => H3.
  apply r_ret. auto.
Qed.


