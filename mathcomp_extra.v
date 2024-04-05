From mathcomp Require Import all_ssreflect. (* from mathcomp *)
From mathcomp Require Import finmap. (* from finmap *)
From mathcomp Require Import mathcomp_extra. (* from analysis *)
From mathcomp Require boolp classical_sets. (* from analysis *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section classical_sets_extra.
Import boolp.
Import classical_sets.
Local Open Scope classical_set_scope.

Lemma Zorn_over T (R : T -> T -> Prop) :
  (forall t, R t t) -> (forall r s t, R r s -> R s t -> R r t) ->
  (forall s t, R s t -> R t s -> s = t) ->
  (forall A : set T, total_on A R -> exists t, forall s, A s -> R s t) ->
  forall u, exists t, R u t /\ forall s, R t s -> s = t.
Proof.
move=> Rrefl Rtrans Rantisym Rtot_max u.
set Tu := ({x : T | R u x}).
set Ru := fun x y : Tu => R (sval x) (sval y).
have Ru_refl x : Ru x x by [].
have Ru_trans x y z : Ru x y -> Ru y z -> Ru x z by apply: Rtrans.
have Ru_antisym : forall x y, Ru x y -> Ru y x -> x = y.
  by move=> [? ?] [? ?] *; exact/eq_exist/Rantisym.
have Ru_tot_max Au : total_on Au Ru -> exists y, forall x, Au x -> Ru x y.
  have [->|] := eqVneq Au set0; first by exists (exist _ u (Rrefl u)).
  move=> /set0P [v Auv] Au_tot.
  pose A := sval @` Au.
  have Atot : total_on A R by move=> x y [xu Axu <-] [yu Ayu <-]; exact: Au_tot.
  have [y ymax] := Rtot_max A Atot.
  have uy : R u y by apply /(Rtrans _ _ _ (svalP v)) /ymax; exists v.
  by exists (exist _ y uy) => x Au_x; apply: ymax; exists x.
have [[x ux] xmax] := Zorn Ru_refl Ru_trans Ru_antisym Ru_tot_max.
exists x; split=> // y xy.
by have /(_ xy)/(congr1 sval) := xmax (exist _ y (Rtrans _ _ _ ux xy)).
Qed.

End classical_sets_extra.

Section boolp_extra.
Import boolp.

Lemma not_andE (P Q : Prop) : (~ (P /\ Q)) = ~ P \/ ~ Q.
Proof. by rewrite propeqE not_andP. Qed.

Lemma contrapE (P : Prop) : (~ ~ P) = P.
Proof.
rewrite propeqE; split; first exact: contrapT.
exact (fun p np => np p).
Qed.

Lemma implyE (P Q : Prop) : (P -> Q) = (~ P \/ Q).
Proof.
by rewrite propeqE -iff_not2 not_implyE not_orP -propeqE contrapE.
Qed.

End boolp_extra.

Section ordinal_ext.
Lemma inord_inj n x y : x < n.+1 -> y < n.+1 -> @inord n x = @inord n y -> x = y.
Proof.
move=> ? ?.
move/(congr1 val).
by rewrite /= !inordK.
Qed.

Lemma inord_eqE n x y :
  x < n.+1 -> y < n.+1 -> (@inord n x == @inord n y) = (x == y).
Proof.
move=> ? ?.
apply/idP/idP; first by move /eqP /inord_inj => /(_ _ _) /eqP; apply.
by move/eqP ->.
Qed.

(* copied from infotheo/lib/ssr_ext.v *)
Lemma ord2 (i : 'I_2) : (i == ord0) || (i == Ordinal (erefl (1 < 2))).
Proof. by case: i => -[|[|]]. Qed.

Lemma ord2_neq0 (x : 'I_2) : (x != ord0) = (x == Ordinal (erefl (1 < 2))).
Proof. by apply/idP/idP; case/orP: (ord2 x) => /eqP ->. Qed.
End ordinal_ext.

Section bigop_ext.

Lemma succn_morph_maxn : {morph succn : x y / maxn x y}.
Proof. by move=> *; rewrite maxnSS. Qed.

Lemma shift_big_plain_seq [R : Type] [idx : R] (op : Monoid.law idx)
      [r : seq R] (P : pred R) (x : R) :
  \big[op/x]_(i <- r | P i) i = op (\big[op/idx]_(i <- r | P i) i) x.
Proof.
rewrite -big_filter -foldrE.
rewrite [in LHS](_ : x = op x idx); last by rewrite Monoid.mulm1.
rewrite -foldr_rcons foldrE -foldl_idx foldl_rcons.
by rewrite -big_filter -foldl_idx.
Qed.

Lemma shift_big_seq [R : Type] [idx : R] (op : Monoid.law idx) [I : eqType]
      [r : seq I] (P : pred I) (F : I -> R) (x : R) :
  \big[op/x]_(i <- r | P i) F i = op (\big[op/idx]_(i <- r | P i) F i) x.
Proof.
have H : forall y, \big[op/y]_(i <- r | P i) F i
                   = \big[op/y]_(u <- [seq F i | i <- r & P i]) u
    by move=> y; rewrite big_map_id big_filter.
rewrite 2!H.
exact: shift_big_plain_seq.
Qed.

Lemma shift_big [R : Type] [idx : R] (op : Monoid.com_law idx)
      [I : finType] (P : pred I) (F : I -> R) (x : R) :
  \big[op/x]_(i | P i) F i = op (\big[op/idx]_(i | P i) F i) x.
Proof.
rewrite -big_filter.
case: big_enumP => ? H ?.
rewrite shift_big_seq.
by rewrite H.
Qed.

Lemma shift_bigmax [I : finType] (P : pred I) (F : I -> nat) (n : nat) :
  \big[maxn/n]_(i | P i) F i = maxn (\max_(i | P i) F i) n.
Proof. exact: shift_big. Qed.

Lemma bigmaxSS [I : finType] (k : I) (P : pred I) (F : I -> nat) :
  P k ->
  \max_(i | P i) (F i).+1 = (\max_(i | P i) (F i)).+1 .
Proof.
move=> pk.
rewrite (@big_morph _ _ succn 1 maxn _ _ succn_morph_maxn) //.
rewrite [in RHS]shift_bigmax.
apply/anti_leq/andP; split; first exact:leq_maxl.
rewrite geq_max; apply/andP; split => //.
by apply: (bigop.bigmax_sup k).
Qed.

Lemma bigmax_ltnP [I : finType] (k : I) (P : pred I) (m : nat) (F : I -> nat) :
  P k -> 
  reflect (forall i : I, P i -> F i < m) (\max_(i | P i) F i < m).
Proof.
move=> pk.
case: m; last first.
  move=> n.
  apply:(iffP idP).
    by move/bigmax_leqP.
  by move=> ?; apply/bigmax_leqP.
apply/(iffP idP); first by rewrite ltn0.
move/(_ k pk).
by rewrite ltn0.
Qed.

End bigop_ext.

Section finmap_ext.
Local Open Scope fset_scope.

Lemma fproperU1 [K : choiceType] (x : K) (A : {fset K}) :
  x \notin A -> A `<` x |` A.
Proof.
move=> xA.
rewrite fproperE; apply/andP; split; first exact: fsubsetU1.
by apply/fsubsetPn; exists x => //; exact: fsetU11.
Qed.

Lemma fdisjointXX [K : choiceType] (A : {fset K}) (x : K) :
  x \in A -> ~ [disjoint A & A]%fset.
Proof. by move=> xA; apply/negP/fset0Pn; exists x; rewrite fsetIid. Qed.

Lemma fdisjointXXP [K : choiceType] (A : {fset K}) :
  reflect (A = fset0) [disjoint A & A]%fset.
Proof.
apply: (iffP idP) => [? | ->].
  apply/eqP/fset0Pn => -[x xA].
  exact: (fdisjointXX xA).
apply/fdisjointP => ?.
by rewrite !in_fset0.
Qed.

Lemma bigfcup_const
      [I : choiceType] [r : seq I] (i0 : I) [P : pred I] :
  i0 \in r -> P i0 ->
  (forall i, i = i0) ->
  \bigcup_(i <- r | P i) [fset i] = [fset i0].
Proof.
move=> i0r Pi0 ii0.
apply/eqP/fset_eqP => i; apply/idP/idP.
- case/bigfcupP => j.
  case/andP => *.
  by rewrite -(ii0 j).
- rewrite inE => /eqP ->.
apply/bigfcupP.
by exists i; rewrite (ii0 i); [apply/andP; split => //| rewrite inE].
Qed.

Lemma cardfs2P (K : choiceType) (A : {fset K}) :
  reflect (exists x y : K, x != y /\ A = [fset x; y]) (#|` A | == 2).
Proof.
apply: (iffP idP); last by case => ? [] ? [] H ->; rewrite cardfs2 H.
move=> /eqP A2.
have : #|` A| != 0 by rewrite A2.
rewrite cardfs_eq0 => /fset0Pn [x xA].
move: A2; rewrite (cardfsD1 x) xA /=.
move/(congr1 Nat.pred).
rewrite add1n -pred_Sn /= => Ax1.
have : #|` A `\ x| != 0 by rewrite Ax1.
rewrite cardfs_eq0 => /fset0Pn [y yAx].
move: Ax1; rewrite (cardfsD1 y) yAx /=.
move/(congr1 Nat.pred).
rewrite add1n -pred_Sn /= fsetDDl => /cardfs0_eq /eqP Axy0.
exists x, y.
split; first by move: yAx; rewrite in_fsetD1 eq_sym => /andP [].
apply/eqP; rewrite eqEfsubset; apply/andP; split; first  by rewrite -fsetD_eq0.
apply/fsubsetP => z.
rewrite inE => /orP []; rewrite in_fset1 => /eqP -> //.
by case/fsetD1P: yAx.
Qed.

Lemma fsetP_val (K : choiceType) (A B : {fset K}) : val A =i val B <-> A = B.
Proof.
split => [vAB | <- //].
apply/fsetP => x.
by rewrite -!topredE /= /pred_of_finset.
Qed.

Lemma cardfs_gt1_sig (K : choiceType) (A : {fset K}) :
  1 < #|` A | -> { xy : K * K | xy.1 != xy.2 /\ xy.1 \in A /\ xy.2 \in A}.
Proof.
move=> A1.
case_eq (val A).
  move/(congr1 size).
  by move: A1 => /[swap] ->.
move=> v vs vvs.
have vs1: 1 <= size vs.
  move/(congr1 size): vvs.
  move: A1 => /[swap] -> /=.
  by rewrite ltnS.
case_eq vs.
  move/(congr1 size).
  by move: vs1 => /[swap] ->.
move=> v' vs' vvs'.
exists (v,v'); split=> //.
  have: uniq [:: v, v' & vs'] by rewrite -vvs' -vvs fset_uniq.
  rewrite uniq_pairwise /=.
  by do ! (move => /andP []).
simpl.
rewrite -!topredE /= /pred_of_finset /= vvs vvs'.
by rewrite !inE !eqxx /= orbT.
Defined.

Lemma cardfs2_sig (K : choiceType) (A : {fset K}) :
  #|` A | = 2 -> { xy : K * K | xy.1 != xy.2 /\ A = [fset xy.1; xy.2]}.
Proof.
move=> A2.
case_eq (val A).
  move/(congr1 size).
  by rewrite A2.
move=> v vs vvs.
have vs1: size vs = 1.
  move/(congr1 size): vvs.
  rewrite /= A2.
  by move/succn_inj => <-.
case_eq vs.
  move/(congr1 size).
  by rewrite vs1.
move=> v' vs' vvs'.
have vs'0: vs' = [::].
  apply: size0nil.
  move: vs1.
  rewrite vvs' /=.
  by move/succn_inj.
exists (v,v'); split=> //.
  have: uniq [:: v, v' & vs'] by rewrite -vvs' -vvs fset_uniq.
  rewrite uniq_pairwise /=.
  by do ! (move => /andP []).
apply/fsetP_val=> x.
by rewrite vvs vvs' vs'0 !inE.
Qed.

Definition fsetT (K : finType) : {fset K} := [fset x | x : K].
(*
Definition fsetT' {K : finType} : {fset K} := [fset x : K | true].
Goal forall K, @fsetT K = @fsetT' K.
Proof.
move=> K.
apply/eqP/fset_eqP=> i.
by rewrite !inE.
Qed.
*)

Lemma in_fsetT (K : finType) x : (x \in fsetT K) = (x \in K).
Proof. by rewrite inE. Qed.

Lemma cardfsT (K : finType) : #|` fsetT K | = #| K |.
Proof. by rewrite cardE card_imfset. Qed.

Lemma fsubsetT (K : finType) (A : {fset K}) : A `<=` fsetT K.
Proof. by apply/fsubsetP=> ?; rewrite inE. Qed.

Lemma fsetTI (K : finType) (A : {fset K}) : A `&` fsetT K = A.
Proof. by apply/eqP; rewrite -/(fsubset _ _) fsubsetT. Qed.

Lemma fsetIT (K : finType) (A : {fset K}) : fsetT K `&` A = A.
Proof. by rewrite fsetIC fsetTI. Qed.

Lemma fsetI_bigcupl (K : choiceType) (I : eqType) (r : seq I)
      (A : {fset K}) (P : pred I) (F : I -> {fset K}) :
  \bigcup_(i <- r | P i) F i `&` A = \bigcup_(i <- r | P i) (F i `&` A).
Proof.
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP => x.
  rewrite inE => /andP [].
  case/bigfcupP => i /andP [ir Pi] xFi xA.
  apply/bigfcupP; exists i; first by apply/andP; split.
  by rewrite inE; apply/andP; split.
case/bigfcupP => i /andP [ir Pi].
rewrite inE => /andP [xFi xA].
rewrite inE; apply/andP; split => //.
by apply/bigfcupP; exists i => //; apply/andP; split.
Qed.

Lemma trivIfset_bigfcupI (T : choiceType) (A : {fset T})
      [P : pred {fset T}] (F : {fset {fset T}}) :
  trivIfset F -> A \in F -> A \notin P ->  \bigcup_(B <- F | P B) B `&` A = fset0.
Proof.
move=> tIF AF AnP.
apply/eqP/fset0Pn.
case => x /[!inE] /andP [] /bigfcupP [] B /andP [BF PB] xB xA.
have : A != B by apply/eqP; move: AnP => /[swap] -> /negP.
move/trivIfsetP: tIF.
move => /(_ A B AF BF) /[apply] /fdisjointP.
by move => /(_ x xA) /negP /(_ xB).
Qed.

Lemma bigfcup_image [aT rT I : choiceType]
      (P : {fset aT}) (f : aT -> I) (F : I -> {fset rT}) :
  \bigcup_(y <- [fset f x | x in P]) F y =
  \bigcup_(x <- P) F (f x).
Proof.
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP => x.
- case/bigfcupP => i.
  rewrite andbT.
  case/imfsetP => y /= yP -> xFfy.
  apply/bigfcupP.
  exists y => //.
  by rewrite andbT.
- case/bigfcupP => y.
  rewrite andbT.
  move=> yP xFfy.
  apply/bigfcupP.
  exists (f y) => //.
  rewrite andbT.
  apply/imfsetP.
  by exists y.
Qed.

Lemma fsetM_seq [K K' : choiceType] (A : {fset K}) (B : {fset K'}) :
 perm_eq (A `*` B) [seq (a, b) | a <- A, b <- B].
Proof.
apply: enum_imfset2 => -[a b] -[c d] _ _ /= abcd.
pose f p := let: (x,y) := p in existT (fun _ : K => K') x y.
change (f (a,b) = f (c,d)).
by rewrite abcd.
Qed.

Lemma cardfsM [K K' : choiceType] (A : {fset K}) (B : {fset K'}) :
  #|` A `*` B | = #|` A | * #|` B |.
Proof.
have:= fsetM_seq A B => /perm_size ->.
by rewrite size_allpairs.
Qed.

Definition fset_diag [K : choiceType] (A : {fset K}) := [fset (x, x) | x in A].

Lemma in_fset_diag [K : choiceType] (A : {fset K}) (a b : K) :
 ((a, b) \in fset_diag A) = (a \in A) && (a == b).
Proof.
apply/idP/idP.
  case/imfsetP=> x /= xA /eqP.
  rewrite xpair_eqE => /andP [] /eqP -> /eqP ->.
  by apply/andP; split.
case/andP=> aA /eqP ab.
apply/imfsetP; exists a => //.
by rewrite ab.
Qed.

Lemma fset_diag_seq [K : choiceType] (A : {fset K}) :
  perm_eq (fset_diag A) [seq (a, a) | a <- A].
Proof.
apply: enum_imfset=> x y _ _.
by move/(eq_ind (x,x) (fun z => x = z.1) erefl _).
Qed.

Definition fset_diagE [K : choiceType] (A : {fset K}) :
  fset_diag A = [fset ((x, y) : K * K) | x in A, y in A & x == y].
Proof.
apply/fsetP => -[a b]; apply/idP/idP.
  case/imfsetP=> x /= ? ->.
  by rewrite in_imfset2 // inE eqxx andbT.
case/imfset2P=> x /= ? [] y /= /[!inE] /andP [] ? /eqP <- ->.
by rewrite in_imfset.
Qed.

Lemma cardfs_diag [K : choiceType] (A : {fset K}) : #|` fset_diag A | = #|` A |.
Proof.
have:= fset_diag_seq A => /perm_size ->.
by rewrite size_map.
Qed.

Lemma fsetMDdiag [K : choiceType] (A : {fset K}) :
  (A `*` A) `\` fset_diag A =
    [fset ((x, y) : K * K) | x in A, y in A & x != y].
Proof.
apply/fsetP => -[a b]; apply/idP/idP.
  rewrite 2!inE /= => /andP /= [] abS /andP [] aS bS.
  rewrite in_imfset2 // inE bS; apply/eqP; move: abS=> /[swap] ->.
  by rewrite in_imfset.
case/imfset2P=> x /= xS [] y /[!inE] /andP [] yS xy ->.
rewrite xS yS !andbT.
apply/negP => /imfsetP [] z /= ? xyz.
move/eqP: xy; apply.
change ((fun p => let: (x,y):= p in x = y) (x,y)).
by rewrite xyz.
Qed.

Lemma fset_diagSM [K : choiceType] (A : {fset K}) : fset_diag A `<=` A `*` A.
Proof.
apply/fsubsetP=> x.
move/imfsetP => /= [] a ? ->.
by rewrite in_imfset2.
Qed.

Lemma fsetM0 [K K' : choiceType] (A : {fset K}) : A `*` @fset0 K' = fset0.
Proof. by apply/eqP/fset0Pn=> -[[a b]]; rewrite inE in_fset0 andbF. Qed.

Lemma fset0M [K K' : choiceType] (A : {fset K'}) : @fset0 K `*` A = fset0.
Proof. by apply/eqP/fset0Pn=> -[[a b]]; rewrite inE in_fset0 andFb. Qed.

Lemma cardfs_diagC [K : choiceType] (A : {fset K}) :
  #|` (A `*` A) `\` fset_diag A | = #|` A | * (#|` A | - 1).
Proof.
case/boolP: (A == fset0).
  by move/eqP ->; rewrite fsetM0 fset0D !cardfs0.
case/fset0Pn=> a aA.
rewrite cardfsD cardfsM.
have := fset_diagSM A => /fsetIidPr ->.
rewrite cardfs_diag (cardfsD1 a A) aA /=.
by rewrite mulnBr muln1.
Qed.

Lemma bipair_fset2_eqE (K : choiceType) (a b c d : K) :
  ([fset (a, b); (b, a)] == [fset (c, d); (d, c)]) = ([fset a; b] == [fset c; d]).
Proof.
apply/idP/idP; move/eqP/fsetP.
  move/(_ (a, b)); rewrite !inE eqxx /= !xpair_eqE => /esym /orP.
  case=> /andP [] /eqP -> /eqP -> //.
  by rewrite fsetUC.
case/boolP: (a == b).
  move/eqP ->; rewrite !fsetUid=> H.
  move/(_ c): (H); rewrite !inE eqxx /=; move=> /eqP ->.
  move/(_ d): (H); rewrite !inE eqxx orbT; move=> /eqP ->.
  by rewrite fsetUid.
move=> /[swap] H.
move/(_ a): (H); rewrite !inE eqxx /= => /esym /orP.
move/(_ b): (H); rewrite !inE eqxx orbT => /esym /orP.
case=> /eqP ->; case=> /eqP ->; rewrite ?eqxx //.
by rewrite fsetUC.
Qed.

Lemma fproperDneq0 (K : choiceType) (A B : {fset K}) :
  A `<` B -> B `\` A != fset0.
Proof.
move/(fsetDpS (fsubset_refl B)).
by rewrite fsetDv fproper0.
Qed.

End finmap_ext.

Section misc.
Local Open Scope fset_scope.

Lemma xorP {b1 b2 : bool} :
  reflect ((b1 = ~~ b2) * (~~ b1 = b2)) (xorb b1 b2).
Proof. by case: b1; case: b2; apply: (iffP idP) => //=; case. Qed.

Lemma eq_span_xor (T : eqType) [x] (a b : T) :
  a != b -> (x == a) || (x == b) = xorb (x == a) (x == b).
Proof.
move=> ab.
apply/idP/idP.
  by move=> /orP [] /eqP ->; rewrite ?(eq_sym b a) (negPf ab) eqxx.
move/xorP ->.
exact: orNb.
Qed.

Lemma fset2_xor [K : choiceType] (x a b : K) :
  a != b -> x \in [fset a; b] = xorb (x == a) (x == b).
Proof. rewrite !inE; exact: eq_span_xor. Qed.

End misc.

Section order_ext.
Import Order.
Import TotalTheory.
Local Open Scope order_scope.
Variables (d : unit) (T : orderType d).
Variables (I : finType) (x : T).
Implicit Types (P : pred I) (F : I -> T).

(* These are fixes to the lemmas of the same name in mathcomp (PR-ed). *)
Lemma eq_bigmax j P F : P j -> (forall i, P i -> x <= F i) ->
  {i0 | i0 \in P & \big[max/x]_(i | P i) F i = F i0}.
Proof.
by move=> Pi0 Hx; rewrite (bigmax_eq_arg _ _ _ _ Pi0) //; eexists => //; case:arg_maxP.
Qed.
Lemma eq_bigmin j P F : P j -> (forall i, P i -> F i <= x) ->
  {i0 | i0 \in P & \big[min/x]_(i | P i) F i = F i0}.
Proof.
by move=> Pi0 Hx; rewrite (bigmin_eq_arg _ _ _ _ Pi0) //; eexists => //; case:arg_minP.
Qed.

End order_ext.
Arguments eq_bigmax {d T I x} j.
Arguments eq_bigmin {d T I x} j.

Section boolp_finmap_extra.
Local Open Scope fset_scope.
Import boolp.
Lemma fsubsetE (K : choiceType) (A B : {fset K}) :
  (A `<=` B) = (forall x, x \in A -> x \in B) :> Prop.
Proof.
rewrite propeqE; split; first by move/fsubsetP.
by move=> ?; apply/fsubsetP.
Qed.

Lemma negE (b : bool) : ~~ b = (~ b) :> Prop.
Proof.
rewrite propeqE; split; first by move/negP.
by move/negP.
Qed.

Lemma swap_imply_head (T U : Type) (P : T -> U -> Prop) :
  (forall t u, P t u) = (forall u t, P t u).
Proof. by rewrite propeqE; split => H *; exact: H. Qed.

Lemma curry_imply_head (T : Type) (P : T -> Prop) (Q : Prop) :
  (forall t, P t -> Q) = ((exists t, P t) -> Q).
Proof.
rewrite propeqE; split; first by move=> H [] t Pt; exact: (H t Pt).
by move=> H t Pt;  exact: (H (ex_intro _ t Pt)).
Qed.

Lemma conj_imply_head (P Q R : Prop) :
  (P -> Q -> R) = (P /\ Q -> R).
Proof.
rewrite propeqE; split; first by move=> ? [].
by move=> H p q; exact: (H (conj p q)).
Qed.

Lemma fset2SE (K : choiceType) (u v : K) (S : {fset K}) :
 ([fset u; v] `<=` S) = ((u \in S) /\ (v \in S)) :> Prop.
Proof.
rewrite propeqE; split.
  by move/fsubsetP=> H; split; [have:= H u | have:= H v];
     rewrite !inE eqxx ?orbT; apply.
by case=> *; apply/fsubsetP=> ?; rewrite !inE=> /orP [] /eqP ->.
Qed.

Lemma eqEfsubset'(K : choiceType) (A B : {fset K}) :
  (A = B) = ((A `<=` B) /\ (B `<=` A)).
Proof.
by rewrite propeqE; split => [/eqP | /andP];
   [rewrite eqEfsubset | rewrite -eqEfsubset] =>[/andP | /eqP].
Qed.

Lemma implyTP (P : Prop) : (True -> P) = P.
Proof. by rewrite propeqE; split; first by apply. Qed.

End boolp_finmap_extra.
