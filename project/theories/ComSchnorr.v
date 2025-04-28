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

Local Open Scope ring_scope.
Import GroupScope GRing.Theory.

From NominalSSP Require Import FsetSolve Group SSProve Nominal NomPackage Disjoint Prelude Sigma Schnorr Reductions.
Import Num.Def Num.Theory Order.POrderTheory.
Import PackageNotation.

From Project Require Import Com.

Module ComSchnorr (GP: GroupParam).

Module S := Schnorr GP.

Module GT := GroupTheorems GP.
Import GP GT S.

#[export] Instance Positive_el : Positive #|el|.
Proof. apply /card_gt0P. by exists g. Qed.

#[export] Instance Positive_exp : Positive #|exp|.
Proof. apply /card_gt0P. by exists 0. Qed.


Definition raw_schnorrCom : raw_sigCom := 
  {| p := raw_schnorr
   ; sampl_wit := 
     {code
       w ← sample uniform #|exp| ;;
       ret w
     }
   ; sampl_challenge := 
     {code 
       e ← sample uniform #|exp| ;;
       ret e
     }
   ; key_gen := λ w,
     {code 
       ret (fto (g ^+ otf w))
     }
  |}.
 
Definition raw_comSchnorr : raw_com := sig_to_com raw_schnorrCom.


Theorem comSchnorr_Correct : Adv_Correct raw_comSchnorr (λ _, 0).
Proof.
  intros A.
  apply eq_ler.
  eapply Adv_perf; [| apply module_valid ].
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel v.
  ssprove_code_simpl_more.
  ssprove_swap_lhs 1%N.
  apply r_const_sample_L => [|w].
  1: apply LosslessOp_uniform.
  apply r_const_sample_L => [|co].
  1: apply LosslessOp_uniform.
  do 2 rewrite otf_fto.
  rewrite eq_refl. simpl.
  rewrite -mulgA. rewrite mulVg. rewrite mulg1. rewrite eq_refl. simpl.
  apply r_ret. auto.

Qed.



Theorem comSchnorr_Hiding : Adv_Hiding raw_comSchnorr (λ _, 0).
Proof.
  intros A.
  eapply le_trans.
  - apply Com_hiding_SHVZK.
    intros. apply NoFail_ret.
  - rewrite -(add0r 0).
    apply lerD.
    + apply: (schnorr_SHVZK {adversary (Transcript raw_schnorr); (A ∘ Call_SHVZK_inp raw_schnorrCom)}).
    + apply: (schnorr_SHVZK {adversary (Transcript raw_schnorr); (A ∘ Call_SHVZK_sam raw_schnorrCom)}).
Qed.


End ComSchnorr.








