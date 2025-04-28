
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

From NominalSSP Require Import FsetSolve Group Nominal NomPackage Disjoint Prelude.
Import Num.Def Num.Theory Order.POrderTheory.
Import PackageNotation.

#[local] Open Scope ring_scope.

Record raw_com := 
    { Key : choice_type
    ; Value : choice_type
    ; Commitment : choice_type 

    ; sampl_key : 
       code fset0 [interface] (Key)

    ; sampl_value : 
    code fset0 [interface] (Value)

    ; locs : {fset Location}

    ; commit :
      ∀ (k : Key) (v : Value),
        code fset0 [interface] (Commitment)

    }.

Notation " 'key p " := (Key p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'value p " := (Value p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'commitment p " := (Commitment p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'key p " := (Key p)
  (at level 3) : package_scope.

Notation " 'value p " := (Value p)
  (at level 3) : package_scope.

Notation " 'commitment p " := (Commitment p)
  (at level 3) : package_scope.





Definition setup_loc : Location := ('bool ; 10%N).
Definition key_loc p : Location := ('key p ; 11%N).
Definition value_loc p : Location := ('value p ; 12%N).

Definition SET_loc := fset [:: setup_loc].
Definition com_locs p : {fset Location} := fset [:: setup_loc ; key_loc p ; value_loc p].

(* Section Correctnes *)

Definition chInputCommit p := (Key p × Value p).

Notation " 'inputCom p " := (chInputCommit p)
     (in custom pack_type at level 2, p constr).

Definition chInputReveal p := (Value p × Commitment p).

Notation " 'inputRev p " := (chInputReveal p)
     (in custom pack_type at level 2, p constr).


Definition RUN := 1%N.


Definition ICorrect p := [interface #val #[ RUN ] : ('inputRev p) → 'bool ].



Definition correct_locs p : {fset Location} := (com_locs p) :|: p.(locs).


    Definition Correct_real p : 
        game (ICorrect p) :=
        [module (com_locs p) ;
           #def #[ RUN ] ('(v, c) : 'inputRev p) : 'bool 
            {
              b ← get setup_loc;;
              #assert (negb b) ;;
              k ← get key_loc p ;;
              c0 ← p.(commit) k v ;;
              if c == c0 then @ret 'bool true else @ret 'bool false

            }
        ].


    Definition Correct_ideal p : 
        game (ICorrect p) :=
        [module no_locs ;
           #def #[ RUN ] ('(v, c) : 'inputRev p) : 'bool 
            {
              @ret 'bool true
            }
        ].

Definition Correct p b :=
  if b then Correct_real p else Correct_ideal p.


Definition Adv_Correct p (ε : adversary (ICorrect p) → Axioms.R) :=
  ∀ A : adversary (ICorrect p), AdvFor (Correct p) A <= ε A.





(* Section Hiding *)


Definition HIDING := 2%N.

Definition IHiding p := [interface #val #[ HIDING ] : ('value p) → 'commitment p ].

    Definition Hiding_real p : 
        game (IHiding p) := 
        [module (com_locs p);
           #def #[ HIDING ] (v : 'value p) : ('commitment p)
            {
              b ← get setup_loc;;
              #assert (negb b) ;;
              k ← get key_loc p ;;
              #put (value_loc p) := v ;;
              c ← p.(commit) k v ;;
              @ret ('commitment p) c 
            }
        ].

    Definition Hiding_ideal p : 
        game (IHiding p) := 
        [module (com_locs p) ; (* nødt til at bruge locs, ellers kan jeg ikke bruge commit *)
           #def #[ HIDING ] (v : 'value p) : ('commitment p)
            {
              b ← get setup_loc;;
              #assert (negb b) ;;
              k ← get key_loc p ;;
              u ← p.(sampl_value) ;;
              #put (value_loc p) := u ;;
              c ← p.(commit) k u ;;
(*               c ← p.(sampl_commitment) ;;  Alternativt skal man bare sample commitment direkte. I det tilfælde kan vi bruge no_locs*)
              @ret ('commitment p) c 
            }
        ].


Definition Hiding p b :=
  if b then Hiding_real p else Hiding_ideal p.


Definition Adv_Hiding p (ε : adversary (IHiding p) → Axioms.R) :=
  ∀ A : adversary (IHiding p), AdvFor (Hiding p) A <= ε A.


Definition Correct_call p : 
    module (IHiding p) (ICorrect p) :=
    [module (com_locs p);
      #def #[ RUN ] ('(v, c) : 'inputRev p) : 'bool 
       {
        #import {sig #[ HIDING ] : ('value p) → 'commitment p} as GenCom ;;
        c0 ← GenCom v ;;
        u ← get value_loc p ;;
        k ← get key_loc p ;;
        c1 ← p.(commit) k u ;;
        if c0 == c1 then @ret 'bool true else @ret 'bool false 

       }
    ].

Lemma Hiding_Correct_perf p (A : adversary (ICorrect p))
  : Adv (Correct_call p ∘ Hiding_real p) (Correct_real p) A = 0.
Proof.
    rewrite -share_link_sep_link; [| nssprove_separate_solve ].
    - eapply Adv_perf; [| exact module_valid ].
      eapply eq_rel_perf_ind_eq.
      simplify_eq_rel vc.
      ssprove_code_simpl.
      destruct vc as [v c].
      ssprove_sync_eq. intros a.
      ssprove_code_simpl_more.
      ssprove_sync_eq => _.
      ssprove_sync_eq. intros k.
      ssprove_swap_lhs 1%N.
  






