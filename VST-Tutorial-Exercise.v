Require Import VST.floyd.proofauto.
Require EV.max3 EV.swap EV.tri EV.gcd EV.append.

(* ################################################################# *)
(** * Task 1: The Max of Three *)

Module Verif_max3.

Import EV.max3.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** C function [max3]:

      int max3(int x, int y, int z)
      {
        if (x < y)
          if (y < z)
            return z;
          else
            return y;
        else
          if (x < z)
            return z;
          else
            return x;
      }

    Specification:
*)

Definition max3_spec :=
 DECLARE _max3
  WITH x: Z, y: Z, z: Z
  PRE  [ _x OF tint, _y OF tint, _z OF tint ]
     PROP  (Int.min_signed <= x <= Int.max_signed;
            Int.min_signed <= y <= Int.max_signed;
            Int.min_signed <= z <= Int.max_signed)
     LOCAL (temp _x (Vint (Int.repr x));
            temp _y (Vint (Int.repr y));
            temp _z (Vint (Int.repr z)))
     SEP   ()
  POST [ tint ]
    EX r: Z, 
     PROP  (r = x \/ r = y \/ r = z;
            r >= x;
            r >= y;
            r >= z)
     LOCAL (temp ret_temp (Vint (Int.repr r)))
     SEP   ().

Definition Gprog : funspecs := ltac:(with_library prog [ max3_spec ]).

Lemma body_max3: semax_body Vprog Gprog f_max3 max3_spec.
Proof.
  start_function.
  (* FILL IN HERE *) 
  forward_if. (* x < y *)
    {
     deadvars.
     forward_if. (* y < z *)
     + {
        forward.
        entailer.
        Exists z.
        entailer.
       }
     + {
        forward.
        Exists y.
        entailer.
       }
     }
    {
     forward_if.
     + {
        forward.
        Exists z.
        entailer.
       }
     + {
        forward.
        Exists x.
        entailer.
       }
    }
Qed.

End Verif_max3.
(** [] *)

(* ################################################################# *)
(** * Task 2: Swap by Arith *)

Module Verif_swap.

Import EV.swap.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** C function [uint_swap_arith]:

      void uint_swap_arith (unsigned int * px, unsigned int * py) {
        * px = * px + * py;
        * py = * px - * py;
        * px = * px - * py;
      }

    Specification:
*)

Definition uint_swap_arith_spec :=
 DECLARE _uint_swap_arith
  WITH x: Z, y: Z, px: val, py: val
  PRE  [ _px OF (tptr tuint), _py OF (tptr tuint) ]
     PROP  ()
     LOCAL (temp _px px; temp _py py)
     SEP   (data_at Tsh tuint (Vint (Int.repr x)) px;
            data_at Tsh tuint (Vint (Int.repr y)) py)
  POST [ tvoid ]
     PROP  ()
     LOCAL ()
     SEP   (data_at Tsh tuint (Vint (Int.repr x)) py;
            data_at Tsh tuint (Vint (Int.repr y)) px).

Definition Gprog : funspecs :=
  ltac:(with_library prog [ uint_swap_arith_spec ]).

Lemma body_uint_swap_arith: semax_body Vprog Gprog
                              f_uint_swap_arith uint_swap_arith_spec.
Proof.
  start_function.
  (* FILL IN HERE *) 
  forward.
  forward.
  forward.
  forward.
  hint.
  autorewrite with norm.
  forward.
  forward.
  forward.
  forward.
  forward.
  autorewrite with norm.
  autorewrite with sublist.
  entailer!.
Qed.

End Verif_swap.
(** [] *)

(* ################################################################# *)
(** * Task 3: Tri *)

Module Verif_tri.

Import EV.tri.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** C program:

      unsigned int tri_for (int n) {
        unsigned int s;
        int i;
        s = 0;
        for (i = 0; i < n; ++ i)
          s = s + i;
        return s;
      }

      unsigned int tri_while (int n) {
        unsigned int s;
        s = 0;
        while (n > 0) {
          n = n - 1;
          s = s + n;
        }
        return s;
      }

    Specification:
*)

Definition tri_spec (_tri_name: ident) :=
 DECLARE _tri_name
  WITH n: Z
  PRE  [ _n OF tint ]
     PROP  (0 <= n <=Int.max_signed)
     LOCAL (temp _n (Vint (Int.repr n)))
     SEP   ()
  POST [ tuint ]
     PROP  ()
     LOCAL (temp ret_temp (Vint (Int.repr (n * (n-1)/2))))
     SEP   ().

Definition Gprog : funspecs :=
  ltac:(with_library prog [ tri_spec _tri_for; tri_spec _tri_while ]).

(** Hint: in your proof, lemma [Z_div_plus_full] and tactic [ring] might be
    helpful. (Ring is just a fancier version of omega which can also handle
    multiplication. *)
Lemma body_tri_for: semax_body Vprog Gprog
                            f_tri_for (tri_spec _tri_for).
Proof.
  start_function.
  (* FILL IN HERE *) 
  forward.
  hint.
  forward_for_simple_bound
  (n)
  (EX i:Z, EX i' : nat,
  PROP( i = Z.of_nat i')
  LOCAL(temp _s (Vint (Int.repr ( ((i-1 )*i)/2 )));
        temp _n (Vint (Int.repr (n)))
  )
  SEP ()
  ).
  { (*Precondition implies the loop invariant*)
    Exists O.
    entailer!.
    }
   
   { (* Loop body preserves the loop invariant*)
    forward.
    Exists (S i'0 ).
    entailer!.
    autorewrite with sublist.
    split.
    + rewrite Nat2Z.inj_succ.
      omega.
    + f_equal.
      f_equal.
      Print Z_div_plus_full.
      assert ( ((Z.of_nat i'0 - 1) * Z.of_nat i'0 + Z.of_nat (i'0) * 2 ) / 2  =
       (Z.of_nat i'0 - 1) * Z.of_nat i'0 / 2 + Z.of_nat i'0 ).
       {
        rewrite Z_div_plus_full.
        ring.
        omega.
       }
       
       rewrite <- H1.
       clear H1.
       f_equal.
       ring.
       }
       
       Intros i'.
       deadvars.
       forward.
       clear Delta.
       entailer!.
       f_equal.
       f_equal.
       f_equal.
       ring.
Qed.

Lemma body_tri_while: semax_body Vprog Gprog
                            f_tri_while (tri_spec _tri_while).
Proof.
  start_function.
  (* FILL IN HERE *) 
  forward.
  forward_while
    (EX n': Z, EX s': Z,
    (*  (s' * 2 = n*(n-1) - n' * (n'-1) )%Z  *)
      (PROP  ( (s' = (n*(n-1) - n' * (n'-1))/2 )%Z; 0 <= n' <=Int.max_signed )
       LOCAL (temp _n (Vint (Int.repr n'));
              temp _s (Vint (Int.repr s')))
       SEP ())).
  { (*Precondition implies loop invariant *)
    Exists n.
    Exists 0.
    
    entailer!.
    autorewrite with sublist.
    auto.
  }
  { (* Loop invariant implies typechecking of loop condition*)
  entailer!.
  }
  { (* Loop body preserves loop invariant.*) 
    forward.
    
    forward.
    autorewrite with norm.
    entailer!.
    Exists ( n'-1 , (n * (n - 1) - n' * (n' - 1)) / 2 + (n' - 1) ).
    unfold fst,snd.
    entailer!.
    hint.
    autorewrite with sublist.
    Print Z_div_plus_full.
    assert(
    (n * (n - 1) - n' * (n' - 1)) / 2 + (n' - 1) = 
    (n * (n - 1) - n' * (n' - 1) + (n' - 1) * 2) / 2 
     ).
     {
     rewrite <- Z_div_plus_full.
     - reflexivity.
     - omega.
     }
     
     rewrite H0.
     f_equal.
     ring.
      }
 (* After Loop *)
  deadvars.
  forward.
  entailer!.
  assert (n'=0).
  {omega. }
  f_equal.
  f_equal.
  clear Delta.
  f_equal.
  rewrite H0.
  ring.
     
Qed.

End Verif_tri.
(** [] *)

(* ################################################################# *)
(** * Task 4: Greatst Common Divisor *)

Module Verif_gcd.

Import EV.gcd.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** C function [gcd]:

      int gcd(int n, int m) {
        int r = m % n;
        if (r == 0)
          return n;
        else
          return gcd(r, n);
      }

    This function calculates the greatest common divisor of two integers.
    [Z.gcd] is defined as part of Coq's standard library. Using this definition,
    we can write specification as follows:
*)

Definition gcd_spec :=
 DECLARE _gcd
  WITH n: Z, m: Z
  PRE  [ _n OF tint, _m OF tint ]
     PROP  (0 < n <= Int.max_signed;
            0 <= m <= Int.max_signed)
     LOCAL (temp _n (Vint (Int.repr n));
            temp _m (Vint (Int.repr m)))
     SEP   ()
  POST [ tint ]
     PROP  ()
     LOCAL (temp ret_temp (Vint (Int.repr (Z.gcd n m))))
     SEP   ().

Definition Gprog : funspecs := ltac:(with_library prog [ gcd_spec ]).

(** We first provide three useful lemmas. You may use it in your proofs. *)

Lemma aux1: forall n, 0 < n <= Int.max_signed -> Int.repr n <> Int.zero.
Proof.
  intros.
  intro.
  apply repr_inj_signed in H0.
  + omega.
  + rep_omega.
    (* This VST tactic is used to handle linear programming with 32-bit bounds.
       You can use it in your own proofs. *)
  + rep_omega.
Qed.

Lemma aux2: forall m, 0 <= m <= Int.max_signed -> Int.repr m <> Int.repr Int.min_signed.
Proof.
  intros.
  intro.
  apply repr_inj_signed in H0.
  + rep_omega.
    (* [rep_omega] can also solve normal linear proof goals. The proof goal
       does not need to be [repable_signed]. *)
  + rep_omega.
  + rep_omega.
Qed.

Lemma mods_repr: forall n m,
  Int.min_signed <= n <= Int.max_signed ->
  Int.min_signed <= m <= Int.max_signed ->
  Int.mods (Int.repr m) (Int.repr n) = Int.repr (Z.rem m n).
(* Here [Z.rem] is the remainder of [m divides n]. *)
Proof.
  intros.
  unfold Int.mods.
  rewrite Int.signed_repr by rep_omega.
  rewrite Int.signed_repr by rep_omega.
  reflexivity.
Qed.

(** Now, fill in the holes in the following proof. *)
Lemma body_gcd: semax_body Vprog Gprog f_gcd gcd_spec.
Proof.
    (* Hint: you can always use [Search] to find useful theorems in Coq's 
       standard library and VST's library. For example, [Z.gcd_rem] may be
       useful. *)
    (* FILL IN HERE *) 
  start_function.
  forward.
  {
    apply aux1 in H.
    apply aux2 in H0.
    entailer!.
    assert ( Int.repr m = Int.repr Int.min_signed ).
    { apply H1. }
    pose proof H2.
    apply H0 in H3.
    exact H3.
    
    (* Hint: remember that you can use [aux1] and [aux2]. *)
    (* FILL IN HERE *) 
  }
  rewrite mods_repr by rep_omega.
  forward_if.
  {
    forward.
    entailer!.
    f_equal.
    f_equal.
    assert (Z.gcd n m = Z.gcd(Z.rem m n) n ).
    {
     rewrite Z.gcd_rem.
     omega.
     rep_omega.
     }
    rewrite H2.
    
    apply repr_inj_signed in H1.
    rewrite H1.
    simpl.
    Search Z.abs.
    rewrite Z.abs_eq.
    reflexivity.
    omega.
    
    assert ( 0 <= Z.rem m n <=m).
    {
    split.
    - apply Z.rem_nonneg.
      omega.
      apply H0.
    - apply Z.rem_le.
      apply H0.
      apply H.
    }
    rep_omega.
    rep_omega. }
(* Z.rem_le: forall a b : Z, 0 <= a -> 0 < b -> Z.rem a b <= a 
   Z.rem_nonneg: forall a b : Z, b <> 0 -> 0 <= a -> 0 <= Z.rem a b
*) 
  {
    assert (Z.rem m n <> 0).
    {
      unfold not; intro.
      rewrite H2 in H1.
      apply H1; reflexivity.
    }
    forward_call (Z.rem m n, n).
    {
    assert ( 0 <= Z.rem m n <=m).
    {
    split.
    - apply Z.rem_nonneg.
      omega.
      apply H0.
    - apply Z.rem_le.
      apply H0.
      apply H.
    }
     omega. 
      (* FILL IN HERE *) 
    }
     forward.
     entailer!.
     f_equal.
     f_equal.
     rewrite Z.gcd_rem.
     reflexivity.
     omega.
    (* FILL IN HERE *) 
  }
  
(* Change it to "Qed." *) 

Qed.

End Verif_gcd.

Module List_seg.

(* ################################################################# *)
(** * Task 5. List Segments *)

Import EV.append.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** In this part, we will verify two C functions:

      struct list {
        unsigned int head;
        struct list * tail;
      };

      unsigned sumlist (struct list *p) {
        unsigned s = 0;
        struct list * t = p;
        unsigned h;
        while (t) {
           h = t->head;
           t = t->tail;
           s = s + h;
        }
        return s;
      }

      struct list *append (struct list *x, struct list *y) {
        struct list *t, *u;
        if (x==NULL)
          return y;
        else {
          t = x;
          u = t->tail;
          while (u!=NULL) {
            t = u;
            u = t->tail;
          }
          t->tail = y;
          return x;
        }
      }

    Using [listrep], we can state their specification.
*)

Definition t_struct_list := Tstruct _list noattr.

Fixpoint listrep (sigma: list Z) (x: val) : mpred :=
 match sigma with
 | h::hs => 
    EX y:val, 
      data_at Tsh t_struct_list (Vint (Int.repr h),y) x  *  listrep hs y
 | nil => 
    !! (x = nullval) && emp
 end.

Arguments listrep sigma x : simpl never.

Definition sum_int (sigma: list Z): Z :=
  fold_right Z.add 0 sigma.

Definition sumlist_spec :=
 DECLARE _sumlist
  WITH sigma : list Z, p: val
  PRE [ _p OF (tptr t_struct_list) ]
     PROP  ()
     LOCAL (temp _p p)
     SEP   (listrep sigma p)
  POST [ tuint ]
     PROP  ()
     LOCAL (temp ret_temp (Vint (Int.repr (sum_int sigma))))
     SEP   (listrep sigma p).

Definition append_spec :=
 DECLARE _append
  WITH x: val, y: val, s1: list Z, s2: list Z
  PRE [ _x OF (tptr t_struct_list) , _y OF (tptr t_struct_list)]
     PROP()
     LOCAL (temp _x x; temp _y y)
     SEP (listrep s1 x; listrep s2 y)
  POST [ tptr t_struct_list ]
    EX r: val,
     PROP()
     LOCAL(temp ret_temp r)
     SEP (listrep (s1++s2) r).

(** Both C functions traverse a linked list using a while loop. Thus, the
    keypoint of verifying them is to write down the correct loop invariant.
    The following diagram demonstrates an intermediate state in traversing.

        +---+---+            +---+---+   +---+---+   +---+---+   
  x ==> |   |  ===> ... ===> |   | y ==> |   | z ==> |   |  ===> ... 
        +---+---+            +---+---+   +---+---+   +---+---+

      | <==== Part 1 of sigma =====> |            | <== Part 2 ==> |

      | <========================== sigma =======================> |

    To properly describe loop invariants, we need a predicate to describe
    the partial linked list from address [x] to address [y]. We provide its
    definition for you. But it is your task to prove its important properties.
*)

Fixpoint lseg (sigma: list Z) (x y: val) : mpred :=
  match sigma with
  | nil => !! (x = y) && emp
  | h::hs => EX u:val, data_at Tsh t_struct_list (Vint (Int.repr h), u) x * lseg hs u y
  end.

Arguments lseg sigma x y : simpl never.

Lemma singleton_lseg: forall (a: Z) (x y: val),
  data_at Tsh t_struct_list (Vint (Int.repr a), y) x |-- lseg [a] x y.
Proof.
intros.
unfold lseg.
entailer!.
Exists y.
entailer!.
Qed.
(* FILL IN HERE *) 
(** [] *)

(** In the next lemma, try to understand how to use [sep_apply]. *)
Lemma lseg_nullval: forall sigma x,
  lseg sigma x nullval |-- listrep sigma x.
Proof.
  intros.
  
  revert x; induction sigma; intros.
  + unfold listrep, lseg.
    entailer!.
  + unfold lseg; fold lseg.
    unfold listrep; fold listrep.
    Intros u.
    Exists u.
    (** The following tactic "apply" [IHsigma] on the left side of derivation. *)
    sep_apply (IHsigma u).
    entailer!.
Qed.

Lemma lseg_lseg: forall (s1 s2: list Z) (x y z: val),
  lseg s1 x y * lseg s2 y z |-- lseg (s1 ++ s2) x z.
Proof.
  intros; revert x y z.
  induction s1; intros.
  - unfold lseg.
    entailer!.
    fold lseg.
    autorewrite with sublist.
    auto.
  - unfold lseg; fold lseg.
    Intros u.
    simpl app.
    unfold lseg; fold lseg.
    Exists u.
    sep_apply IHs1.
    entailer!.
 
 Qed.
    
(* FILL IN HERE *) 
(** [] *)

Lemma lseg_list: forall (s1 s2: list Z) (x y: val),
  lseg s1 x y * listrep s2 y |-- listrep (s1 ++ s2) x.
Proof.
  intros; revert x y .
  induction s1;intros.
  - unfold lseg .
    entailer!.
    apply derives_refl.
  - unfold lseg ; fold lseg.
    Intros u.
    simpl app.
    Exists u.
    entailer!.
    auto.
Qed.
     
(* FILL IN HERE *) 
(** [] *)

(** Try to use prove the following assertion derivation use the lemmas above.
    The first step is done for you. *)
Example lseg_ex: forall s1 s2 s3 x y z,
  lseg s1 x y * lseg s2 y z * lseg s3 z nullval |-- listrep (s1 ++ s2 ++ s3) x.
Proof.
  intros.
  sep_apply (lseg_lseg s2 s3 y z nullval).
  sep_apply (lseg_lseg s1 (s2 ++ s3) x y nullval).
  sep_apply (lseg_nullval (s1 ++ s2 ++ s3) x ).
  auto.
  (* FILL IN HERE *) 
Qed.
(** [] *)

(* ################################################################# *)
(** * Task 6. Sum of a List *)

(** Now, you are going to prove [sumlist] correct. The following lemmas are
    copied from [verif_reverse2] for proof automation. *)

Lemma listrep_local_facts:
  forall sigma p,
   listrep sigma p |--
   !! (is_pointer_or_null p /\ (p=nullval <-> sigma=nil)).
Proof.
intros.
revert p; induction sigma; 
  unfold listrep; fold listrep; intros; normalize.
apply prop_right; split; simpl; auto. intuition.
entailer!.
split; intro. subst p. destruct H; contradiction. inv H2.
Qed.

Hint Resolve listrep_local_facts : saturate_local.

Lemma listrep_valid_pointer:
  forall sigma p,
   listrep sigma p |-- valid_pointer p.
Proof.
 destruct sigma; unfold listrep; fold listrep;
 intros; normalize.
 auto with valid_pointer.
 apply sepcon_valid_pointer1.
 apply data_at_valid_ptr; auto.
 simpl;  computable.
Qed.

Hint Resolve listrep_valid_pointer : valid_pointer.

Module sumlist.

(** Another auxiliary lemma. Hint: use [Search] when you need to find a
    lemma. *)
Lemma sum_int_snoc:
  forall a b, sum_int (a++b :: nil) = (sum_int a) + b.
Proof.
  intros.
  induction a.
  - simpl.
    ring.
  - simpl.
  rewrite IHa.
  ring.
  Qed.
(* FILL IN HERE *) 
(** [] *)


Definition Gprog : funspecs :=
  ltac:(with_library prog [ sumlist_spec ]).

(*      unsigned sumlist (struct list *p) {
        unsigned s = 0;
        struct list * t = p;
        unsigned h;
        while (t) {
           h = t->head;
           t = t->tail;
           s = s + h;
        }
        return s;
      }
 *)

(** Hint: take a look at Verif_reverse and learn its proof strategy. *)
Lemma body_sumlist: semax_body Vprog Gprog f_sumlist sumlist_spec.
Proof.
  start_function.
  forward.
  forward. 
  forward_while(
   EX t : val ,
   EX L: list Z,
   EX L' : list Z,
   EX s : Z,
   PROP( L ++ L' =sigma ;
    s = fold_left Z.add L 0 
    )
   LOCAL(temp _t t; temp _p p ; temp _s (Vint (Int.repr s)))
   SEP(lseg L p t; listrep L' t  )
   ).
   { (*    Precondition implies loop invariant.    *)
   entailer!.
   Exists p (@nil Z) sigma 0.
   autorewrite with sublist.
   entailer!.
   unfold lseg.
   entailer!.   
   }
   { (* loop invariant implies typechecking *)
   entailer!.
   }
   { (* loop invariant preserves *)
    assert_PROP (L' <> nil).
    {
     entailer!.
     pose proof proj2 H1 eq_refl.
     subst.
     apply HRE.
    }
    destruct L' as [|s2a s2b];[congruence | clear H1].
    unfold listrep ; fold listrep.
    Intros y.
    forward.
    forward.
    forward.
    entailer!.
    Exists (y,L++[s2a] ,s2b ,  (fold_left Z.add (L++ [s2a] )0) ).
    (*  Exists val * list * list * Z  *)
    entailer!.
    +  split.
     ++ rewrite app_ass.
     auto.
     ++ f_equal.
        f_equal.
        Search fold_left.
       rewrite fold_left_app.
       auto.
    + unfold lseg; fold lseg.
      unfold listrep. fold listrep.
      cancel.
      assert (data_at Tsh t_struct_list
  (Vint (Int.repr s2a), y) t  |-- lseg [s2a] t y).
    { unfold lseg.
      Exists y.
      entailer!.
      }
      
      assert (lseg L p t * lseg [s2a] t y |-- lseg (L ++[s2a]) p y ).
      {
       apply lseg_lseg.
       }
      
      assert (lseg L p t *
data_at Tsh t_struct_list
  (Vint (Int.repr s2a), y) t |--lseg L p t * lseg [s2a] t y).
  {
   hint.
   entailer!.
  }
  sep_apply H4.
  sep_apply H0.
  auto.
  }
  forward.
entailer!.
  assert ( L' = []).
  { apply H1. auto. }
  rewrite H.
- f_equal.
  f_equal.
  clear Delta.

  autorewrite with sublist.
  unfold sum_int.
  Search fold_left.
  rewrite fold_symmetric. 
  * auto.
  * intros.
    ring.
  * intros.
    ring.
-   assert ( L' = []).
  { apply H1. auto. }
  rewrite H.
    autorewrite with sublist.
  sep_apply lseg_list.
  autorewrite with sublist.
  
  auto.
  
  Qed.
    
      
(* FILL IN HERE *) 
(** [] *)

End sumlist.

(* ################################################################# *)
(** * Task 7: Append *)

Module append.

Definition Gprog : funspecs :=
  ltac:(with_library prog [ append_spec ]).

(* struct list *append (struct list *x, struct list *y) {
  struct list *t, *u;
  if (x==NULL)
    return y;
  else {
    t = x;
    u = t->tail;
    while (u!=NULL) {
      t = u;
      u = t->tail;
    }
    t->tail = y;
    return x;
  }
}

Definition append_spec :=
 DECLARE _append
  WITH x: val, y: val, s1: list Z, s2: list Z
  PRE [ _x OF (tptr t_struct_list) , _y OF (tptr t_struct_list)]
     PROP()
     LOCAL (temp _x x; temp _y y)
     SEP (listrep s1 x; listrep s2 y)
  POST [ tptr t_struct_list ]
    EX r: val,
     PROP()
     LOCAL(temp ret_temp r)
     SEP (listrep (s1++s2) r).
 *)
 
Lemma body_append: semax_body Vprog Gprog f_append append_spec.
Proof.
  start_function.
  forward_if.
  { (* x == NULL *)
   forward.
   Exists y.
   entailer!.
   assert ( s1 = nil ).
   { apply H0.
     auto. 
   }
   subst s1.
   unfold listrep at 1.
   simpl app.
   entailer!.
   }
   
   { forward.
     assert_PROP(exists s1a s1b, s1 = s1a::s1b).
     { entailer!.
       destruct s1.
       + rewrite H0 in H.
         contradiction.
       + eauto.
     }
     destruct H0 as [ s1a [ s1b ?]].
     subst s1.
     unfold listrep at 1; fold listrep.
     Intros x'.
     forward.
     
     forward_while(
        EX (t u:val) (L1 L3 : list Z) ( a : Z),
        
        PROP( 
              L1 ++[a] ++ L3 = s1a :: s1b
              (* t -> u  :  data_at 关系
              :  (data_at Tsh t_struct_list (Vint (Int.repr a ),u ) t)%assert
              *)
            )
        LOCAL(
            temp _t t;
            temp _x x;
            temp _y y;
            temp _u u
            )
        SEP(lseg L1 x t;
            listrep L3 u;
            lseg [a] t u;
            listrep s2 y
             )
     ).
     {  (* Precondition *) 
      Exists x x' (@nil Z) s1b s1a.
      autorewrite with sublist.
      entailer!.
      unfold lseg.
      Exists x'.
      entailer!.
      }
     { entailer!. }
     { (* Preserves *)
      forward.
      assert_PROP( L3<>nil).
      { entailer!.
        pose proof proj2 H1 eq_refl.
        subst.
        apply HRE. reflexivity.
        }        
     destruct L3 as [|L3a L3b]; [congruence | clear H1].
     
     unfold listrep ; fold listrep.
     Intros y0.
     forward.
     entailer!.
     Exists (u,y0,L1 ++ [a] ,L3b , L3a).
     entailer!.
     + rewrite app_ass.
       auto.
     + unfold listrep; fold listrep.
       cancel.
       assert ( lseg L1 x t * lseg [a] t u |--lseg (L1++[a]) x u  ).
       { apply lseg_lseg. }
       sep_apply H5. cancel.
       apply singleton_lseg.
       }
   { (* After loop*)
     subst u.
     assert_PROP( L3 = [] ).
     { entailer!.
       pose proof proj1 H1 .
       apply H3.
       reflexivity.
     }
     rewrite H1 in H0.
     rewrite H1.
     
     unfold lseg;fold lseg.
     Intros u.
     forward.
     subst u.
     clear H1.
     forward.
     Exists x.
     entailer!.
     sep_apply singleton_lseg.
     sep_apply lseg_list.
     sep_apply lseg_list.
     autorewrite with sublist in *|-.
     rewrite <- H0.
     assert (L1 ++ [a] ++ s2 = (L1 ++ [a]) ++ s2 ).
     { rewrite  app_assoc_reverse. auto. }
     rewrite H5.
     cancel.
     unfold listrep. (*who can imagine all what we need is just need a "unfold" ?*)
     entailer!.
   }
   }
   Qed. 
     
(* FILL IN HERE *) 
(** [] *)

End append.

(* ################################################################# *)
(** * Task 8: List box segments *)

(** Now, consider this alternative implementation of append:

      void append2(struct list * * x, struct list * y) {
        struct list * h;
        h = * x;
        while (h != NULL) {
          x = & (h -> tail);
          h = * x;
        }
        * x = y;
      }

    You should prove:
*)

Module append2.

(* void append2(struct list * * x, struct list * y) {
  struct list * h;
  h = * x;
  while (h != NULL) {
    x = & (h -> tail);
    h = * x;
  }
  * x = y;
}
 *)

Definition append2_spec :=
 DECLARE _append2
  WITH x: val, y: val, s1: list Z, s2: list Z, p :val
  PRE [ _x OF (tptr (tptr t_struct_list)) , _y OF (tptr t_struct_list)]
     PROP()
     LOCAL (temp _x x; temp _y y)
     SEP (data_at Tsh (tptr t_struct_list) p x;
          listrep s1 p;
          listrep s2 y)
  POST [ tvoid ]
     EX q: val,
     PROP()
     LOCAL()
     SEP (data_at Tsh (tptr t_struct_list) q x;
          listrep (s1 ++ s2) q).

Definition Gprog : funspecs :=
  ltac:(with_library prog [ append2_spec ]).

(** You may find it inconvenient to complete this proof directly using [listrep]
    and [lseg]. You may need another predicate for [list box segment].

         +---+---+            +---+---+   +---+---+   +---+---+   
   p ==> |   |  ===> ... ===> |   |   ==> |   |   ==> |   |  ===> ... 
         +---+---+            +---+---+   +---+---+   +---+---+

       | <====            list segment      =====> |

 | <====           list box segment     =====> |

    Try to define this predicate by yourself and prove [lbseg_lseg].
*)


Fixpoint lbseg (sigma: list Z) (x y: val) : mpred :=
 match sigma with 
 | nil => !! ( x = y ) && emp
 | h :: hs => EX (u: val) , 
              data_at Tsh (tptr t_struct_list ) u x *
              field_at Tsh t_struct_list [StructField _head] (Vint (Int.repr h )) u *
              lbseg hs (field_address t_struct_list [StructField _tail] u) y
end.
(* Fixpoint lseg (sigma: list Z) (x y: val) : mpred :=
  match sigma with
  | nil => !! (x = y) && emp
  | h::hs => EX u:val, data_at Tsh t_struct_list (Vint (Int.repr h), u) x * lseg hs u y
  end.
 *)
(* FILL IN HERE *) 
(** [] *)

Lemma lbseg_lseg: forall s3 x y z,
  lbseg s3 x y * data_at Tsh (tptr t_struct_list) z y |--
  EX y', data_at Tsh (tptr t_struct_list) y' x*lseg s3 y' z.
Proof.
  intros.
  revert x y z.
  induction s3.
  - unfold lbseg . unfold  lseg.
    entailer!.
    Exists z.
    entailer!.
  - 
    intros.
    unfold lbseg.
    fold lbseg.
    Intros u.
    Exists u.
    sep_apply IHs3.
    Intros y'.
    unfold lseg at 2.
    Exists y'.
    fold lseg.
    entailer!.
    unfold_data_at (data_at Tsh t_struct_list _ _).
    entailer!.
    Qed.
(* FILL IN HERE *) 
(** [] *)
(* 
(** Hint: adding more lemmas for [lbseg] may be useful. *) *)
Lemma lbseg_app : forall L1 L2a x t h ,
          lbseg L1 x t *
          field_at Tsh t_struct_list [StructField _head]  (Vint (Int.repr L2a)) h *
          data_at Tsh (tptr t_struct_list) h t
          |-- lbseg (L1 ++ [L2a]) x (field_address t_struct_list [StructField _tail] h).
Proof.
        intros L1.
        induction L1.
        - intros.
           unfold lbseg; fold lbseg.
           
           Exists h.
           entailer!.
           
        -  intros.
           unfold lseg; fold lseg.
           rewrite <-app_comm_cons.
           unfold lbseg; fold lbseg.
           Intros u. Exists u.
           entailer!.
           sep_apply IHL1.
           auto.
Qed.


Lemma body_append2: semax_body Vprog Gprog f_append2 append2_spec.
Proof.
  start_function.    
  forward. (* h = *x *)
  forward_while
  (
   EX (t :val )(h:val)
      (L1 L2 :list Z),
   PROP (  L1 ++ L2 = s1   )
   LOCAL (
        temp _y y ;
        temp _x t ;
        temp _h h
         )
   SEP (
       listrep s2 y;
       (* y....
          <-->
       *)  
       lbseg L1 x t;
       (* p....h.....
          ↑<-->↑
          x    t
       *)  
       listrep L2 h;
       (* p....h.....
          ↑    ↑<...>
          x    t
       *)
       data_at Tsh (tptr t_struct_list) h t(*当前x*)
       )
       )%assert.
   { (* Precondition *)
     entailer!.
     Exists x p (@nil Z) s1.
     entailer!.
     unfold lbseg.
     entailer!.
   }
   { entailer!.
   }
   { 
     assert_PROP(L2<>[]).
     { entailer!. 
        pose proof proj2 H1 .
        apply HRE in H.
        auto.
        auto.
      }
      forward.
    
    - (*可计算性*)
       entailer!.
       unfold is_pointer_or_null in PNh.
       unfold nullval in HRE.
       destruct h; auto.
       destruct Archi.ptr64;auto.
       rewrite PNh in HRE. 
       contradiction.
    - autorewrite with norm.
      destruct L2 as [|L2a L2b];       [exfalso; auto|subst].
      unfold listrep; fold listrep.
      simpl.
      Intros y0.
      
      unfold_data_at (data_at Tsh t_struct_list _ _).
(*       forward.
      Print offset_val. *)
      assert_PROP (offset_val 4 h = field_address t_struct_list [StructField _tail] h ).
      { entailer!.
(*         Search field_address. *)
        rewrite field_address_offset.
        auto. auto.
      }
      forward.
      entailer!.
      Exists ( field_address t_struct_list [StructField _tail] h,y0 ,L1 ++ [L2a], L2b ).
      entailer!.
      + rewrite <- app_assoc. auto.
      + entailer!.
        sep_apply lbseg_app.
        auto.
     }
     forward.
     sep_apply lbseg_lseg.
     Intros y'. Exists y'.
     entailer!.
     pose proof proj1 H3 eq_refl.
     entailer!.
     unfold listrep;fold listrep.
     
     rewrite app_nil_r.
     sep_apply lseg_list.
     entailer!.
Qed.
        
   
  
(* FILL IN HERE *) 
(** [] *)

End append2.

End List_seg.
