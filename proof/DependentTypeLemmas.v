(*******************************************************************************)
(*  © Université Lille 1, The Pip Development Team (2015-2016)                 *)
(*                                                                             *)
(*  This software is a computer program whose purpose is to run a minimal,     *)
(*  hypervisor relying on proven properties such as memory isolation.          *)
(*                                                                             *)
(*  This software is governed by the CeCILL license under French law and       *)
(*  abiding by the rules of distribution of free software.  You can  use,      *)
(*  modify and/ or redistribute the software under the terms of the CeCILL     *)
(*  license as circulated by CEA, CNRS and INRIA at the following URL          *)
(*  "http://www.cecill.info".                                                  *)
(*                                                                             *)
(*  As a counterpart to the access to the source code and  rights to copy,     *)
(*  modify and redistribute granted by the license, users are provided only    *)
(*  with a limited warranty  and the software's author,  the holder of the     *)
(*  economic rights,  and the successive licensors  have only  limited         *)
(*  liability.                                                                 *)
(*                                                                             *)
(*  In this respect, the user's attention is drawn to the risks associated     *)
(*  with loading,  using,  modifying and/or developing or reproducing the      *)
(*  software by the user in light of its specific status of free software,     *)
(*  that may mean  that it is complicated to manipulate,  and  that  also      *)
(*  therefore means  that it is reserved for developers  and  experienced      *)
(*  professionals having in-depth computer knowledge. Users are therefore      *)
(*  encouraged to load and test the software's suitability as regards their    *)
(*  requirements in conditions enabling the security of their systems and/or   *)
(*  data to be ensured and,  more generally, to use and operate it in the      *)
(*  same conditions as regards security.                                       *)
(*                                                                             *)
(*  The fact that you are presently reading this means that you have had       *)
(*  knowledge of the CeCILL license and that you accept its terms.             *)
(*******************************************************************************)

(** * Summary 
    This file contains required lemmas to help in proving some properties
    on our dependent types defined into [Model.ADT] *)
Require Import Model.ADT  Model.Hardware Model.MAL Arith Model.Lib StateLib.
Require Import Coq.Logic.ProofIrrelevance Omega.

(** ADT : level **)
Lemma levelEqBEqNatTrue :
forall l l' : level, StateLib.Level.eqb l l' = true -> l = l' .
 Proof.
 intros l l' H.  
 unfold StateLib.Level.eqb in H. 
 apply beq_nat_true in H.
 destruct l.
 destruct l'. simpl in *.
 subst.
 assert (Hl = Hl0).
 apply proof_irrelevance. subst. intuition.
Qed.

Lemma levelEqBEqNatFalse0 : 
forall l ,
StateLib.Level.eqb l fstLevel = false -> l > 0.
Proof.
intros.
unfold StateLib.Level.eqb in H.
apply beq_nat_false in H.
unfold fstLevel in H.
unfold CLevel in H.
case_eq (lt_dec 0 nbLevel).
intros.
rewrite H0 in H.
simpl in *. omega.
intros.
assert (0 < nbLevel). 
apply nbLevelNotZero.
contradict H1.
intuition. 
Qed. 

Lemma CLevel0_r :  forall l : level,l - CLevel 0 = l. 
Proof. 
unfold CLevel.
case_eq (lt_dec 0 nbLevel).
intros.
simpl. omega.
intros.
assert (0 < nbLevel).
apply nbLevelNotZero. omega.
Qed.

Lemma CLevelIdentity : forall l : level, CLevel (l - CLevel 0) = l.
Proof.
intros l.
rewrite CLevel0_r. destruct l.
simpl.
unfold CLevel. 
case_eq(lt_dec l nbLevel).
intros. simpl.
assert ( Hl = ADT.CLevel_obligation_1 l l0).
apply proof_irrelevance.
subst. reflexivity.
intros.
contradict H. 
omega.
Qed.

Lemma CLevelIdentityLe :
forall a , a < nbLevel ->  a <= CLevel a.
Proof.
intros.
unfold CLevel.
case_eq (lt_dec a nbLevel); intros.
simpl; omega.
now contradict H.
Qed.

Lemma levelPredMinus1: forall l l' , StateLib.Level.eqb l fstLevel = false -> StateLib.Level.pred l = Some l' -> l' = CLevel (l - 1).
Proof.
intros. 
unfold StateLib.Level.pred  in *.
assert (l > 0).
{ apply levelEqBEqNatFalse0.
  assumption. }
case_eq (gt_dec l 0).
* intros.
  rewrite H2 in H0.
  inversion H0.
  unfold CLevel.
  case_eq (lt_dec (l - 1) nbLevel).
  intros. subst.   
  assert (ADT.CLevel_obligation_1 (l - 1) l0  = StateLib.Level.pred_obligation_1 l g ).
  apply proof_irrelevance. 
  rewrite H4. reflexivity.
  intros.
  destruct l.
  subst. 
  simpl in *.
  contradict H3.
  omega.
* intros.
  contradict H1.
  assumption.
Qed.

Lemma levelEqNat : 
forall a b , a < nbLevel -> b < nbLevel -> CLevel a = CLevel b -> a = b.
Proof.
intros a b Ha Hb Hab.
 unfold CLevel in *.
 case_eq (lt_dec a nbLevel );intros g Ha'.
 + rewrite Ha' in Hab.
   case_eq (lt_dec b nbLevel);intros p Hb'.
   - rewrite Hb' in Hab.
     inversion Hab. intuition.
   - omega.
 + omega.  
Qed.

Lemma level_gt : 
forall x x0, x - x0 < nbLevel ->  CLevel (x - x0) > 0 -> x > x0.
Proof.
intros.
unfold CLevel in *.
case_eq (lt_dec (x - x0) nbLevel ).
intros. rewrite H1 in H0.
simpl in *. omega.
intros. contradict H1. omega.       
Qed.   

(**** ADT : page **)
Lemma isDefaultPageFalse : forall p,   (defaultPage =? pa p) = false -> pa p <> defaultPage .
Proof.
intros. 
apply beq_nat_false in H.
unfold not. intros.
contradict H. symmetry.
unfold defaultPage in *.
unfold CPage in *.
case_eq (lt_dec 0 nbPage).
intros.
rewrite H in H0.
rewrite H0. trivial.
intros.
rewrite H in H0. rewrite H0. intuition.
Qed.

Lemma isDefaultPageTrue : forall p,   (defaultPage =? pa p) = true -> pa p = defaultPage .
Proof.
intros. 
apply beq_nat_true in H. symmetry.
unfold defaultPage in *.
unfold CPage in *.
case_eq (lt_dec 0 nbPage).
intros.
rewrite H0 in H.
symmetry.
simpl in *.
destruct p.
simpl in *. 
subst.
destruct pa.
simpl in *.
subst.
assert (Hp = ADT.CPage_obligation_1 0 l ).
apply proof_irrelevance.
subst.
intuition.
intros.
rewrite H0 in H.
subst.
simpl in *.
destruct p.
simpl in *. 
subst.
destruct pa.
simpl in *.
subst.
destruct page_d.
simpl in *.
assert (Hp = Hp0).
apply proof_irrelevance.
subst.
intuition.
Qed.


(** ADT : index **)
Lemma indexEqFalse : 
forall a b : nat , a < tableSize -> b < tableSize -> a <> b -> CIndex a <> CIndex b.
Proof.
intros.
unfold CIndex.
case_eq (lt_dec a tableSize).
+ intros.
  case_eq (lt_dec b tableSize).
  - intros.
    unfold not in *.
    intros.
    apply H1.
    inversion H4.
    intuition.
  - intros. contradict H0. assumption.
+ intros. contradict H. intuition.
Qed. 

Lemma indexltbTrue : 
forall i1 i2 : index , 
StateLib.Index.ltb i1 i2 = true -> i1 < i2.
Proof. intros. unfold MALInternal.Index.ltb in H. 
apply NPeano.Nat.ltb_lt in H.
assumption.
Qed. 

Lemma indexltbFalse : 
forall i1 i2 : index , 
StateLib.Index.ltb i1 i2 = false -> i1 >= i2.
Proof.
intros.
unfold MALInternal.Index.ltb in *. 
apply not_lt.
apply NPeano.Nat.ltb_nlt in H.
omega.  
Qed. 

Lemma indexBoundEq : 
forall i : index , i>= CIndex (tableSize - 1) -> i =  CIndex (tableSize - 1). 
Proof.
intros.
unfold CIndex in *.
destruct (lt_dec (tableSize - 1) tableSize).
simpl in *.
destruct i.
simpl in *. 
subst.
assert(i = tableSize - 1). omega. 
subst. 
assert (Hi = ADT.CIndex_obligation_1 (tableSize - 1) l ).
apply proof_irrelevance.
subst. trivial.
contradict n.
assert (0 < tableSize).
assert (tableSize > tableSizeLowerBound). 
apply tableSizeBigEnough.
unfold  tableSizeLowerBound in * . omega. omega. 
Qed.

Lemma indexDiffLtb :
forall i1 i2 : index, i2 < i1 \/ i1 < i2 <-> i2 <> i1.
Proof.
intros.
split;destruct i1, i2;
simpl in *.
 unfold not;
intros;
inversion H0; omega.
intros.
apply nat_total_order.
unfold not in *; intros; subst.
apply H; f_equal.
apply proof_irrelevance.
Qed.

Lemma indexEqId : 
forall i : index, CIndex i = i. 
Proof.
intros.
unfold CIndex.
destruct i.
simpl.
case_eq(lt_dec i tableSize); intros.
assert(ADT.CIndex_obligation_1 i l = Hi) by apply proof_irrelevance.
subst. reflexivity.
now contradict Hi.
Qed.

Lemma indexMaxEqFalseLt : 
forall idx : index, idx <> CIndex (tableSize - 1) -> idx < tableSize - 1.
Proof.
intros.
unfold CIndex in *.
case_eq (lt_dec (tableSize - 1) tableSize).
intros .
rewrite H0 in *.
destruct idx.
simpl in *.
apply not_ge.
unfold not.
intros.
contradict H.
assert (i = tableSize - 1).
omega.
subst.
f_equal.
apply proof_irrelevance.
intros.
assert(tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
omega.
Qed.

Lemma indexMaxEqFalseLt1 : 
forall idx : index, idx <> CIndex (tableSize - 1) -> idx < CIndex (tableSize - 1).
Proof.
intros.
unfold CIndex in *.
case_eq (lt_dec (tableSize - 1) tableSize).
intros .
rewrite H0 in *.
destruct idx.
simpl in *.
apply not_ge.
unfold not.
intros.
contradict H.
assert (i = tableSize - 1).
omega.
subst.
f_equal.
apply proof_irrelevance.
intros.
assert(tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
omega.
Qed.

Lemma noteqIndex a b:
a < tableSizeLowerBound -> b < tableSizeLowerBound -> a<>b ->  
CIndex a <> CIndex b.
Proof.
intros. 
apply indexEqFalse;
assert (tableSize > tableSizeLowerBound).
apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
omega.  apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
omega. apply tableSizeBigEnough. omega.
Qed.

Lemma indexEqbTrue : 
forall idx1 idx2 : index, true = StateLib.Index.eqb idx1 idx2 -> 
idx1 = idx2.
Proof.
unfold StateLib.Index.eqb in *.
intros.
symmetry in H.
apply beq_nat_true in H.
destruct idx1; destruct idx2.
simpl in *.
subst.
f_equal.
apply proof_irrelevance.
Qed.

Lemma indexLtZero : 
forall idx : index, idx < CIndex 0 -> False.
Proof.
intros.
unfold CIndex in *.
case_eq (lt_dec 0 tableSize); intros; rewrite H0 in *.
destruct idx. simpl in *.
omega.
assert (tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
omega.
Qed.

Lemma indexSEqbZeroOdd : 
forall curidx idxsucc, 
true = StateLib.Index.eqb curidx (CIndex 0) -> 
StateLib.Index.succ curidx = Some idxsucc -> 
Nat.Odd idxsucc.
Proof.
intros.
apply indexEqbTrue in H.
subst.
unfold Index.succ in *.
case_eq (lt_dec (CIndex 0 + 1) tableSize); intros; rewrite H in *.
inversion H0.
destruct idxsucc.
inversion H2.
subst.
unfold Nat.Odd.
eexists 0.
simpl.
unfold CIndex.
case_eq (lt_dec 0 tableSize); intros.
simpl. trivial.
assert (tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
omega.
now contradict H0.
Qed.

Lemma indexZeroNotOdd : 
forall idx idxsucc : index,
idx < idxsucc -> 
StateLib.Index.succ (CIndex 0) = Some idxsucc ->
~ Nat.Odd idx.
Proof.
intros.
unfold Index.succ in *.
case_eq (lt_dec (CIndex 0 + 1) tableSize); intros; rewrite H1 in *.
inversion H0.
destruct idxsucc.
inversion H3.
subst.
clear H0 H3.
simpl in *.
unfold CIndex in H.
case_eq (lt_dec 0 tableSize); intros.
simpl. rewrite H0 in *.
simpl in *.
unfold not.
intros.
unfold Nat.Odd in *.
destruct H2.
rewrite H2 in *.
omega.
assert (tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
omega.
now contradict H0.
Qed.
 
 Lemma indexSEqbZeroLt : 
forall  idxsucc idx : index, 
StateLib.Index.succ (CIndex 0)  = Some idxsucc -> 
idx < idxsucc -> 
idx = CIndex 0.
Proof.
intros.
unfold Index.succ in *.
case_eq (lt_dec (CIndex 0 + 1) tableSize); intros; rewrite H1 in *.
inversion H.
destruct idxsucc.
inversion H3.
subst.
clear H H3 H1  l.
simpl in *.
unfold CIndex in *.
case_eq (lt_dec 0 tableSize); intros; rewrite H in *.
simpl in *.
destruct idx.
simpl in *.
destruct i.
f_equal.
apply proof_irrelevance.
omega.
assert (tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
omega.
now contradict H0.
Qed.

Lemma indexSuccGt : 
forall idx curidx iIndex : index,
StateLib.Index.succ curidx = Some iIndex -> 
idx < curidx -> 
idx <> iIndex.
Proof.
intros.
unfold Index.succ in *.
case_eq (lt_dec(curidx + 1) tableSize); intros; rewrite H1 in *.
simpl in *.
destruct idx.
simpl in *.
destruct iIndex.
inversion H.
unfold not; intros.
inversion H2.
subst.
omega.
now contradict H.
Qed.

Lemma indexSuccEqFalse: 
forall  curidx iIndex : index,
StateLib.Index.succ curidx = Some iIndex -> 
 curidx <> iIndex.
Proof.
intros.
unfold Index.succ in *.
case_eq (lt_dec(curidx + 1) tableSize); intros; rewrite H0 in *.
simpl in *.
destruct iIndex.
inversion H.
subst.
clear H.
unfold not; intros.
destruct curidx.
simpl in *.
inversion H.
omega.
now contradict H.
Qed.

Lemma indexSuccSuccOddOr (curidx iIndex nextidx idx : index): 
StateLib.Index.succ curidx = Some iIndex ->
StateLib.Index.succ iIndex = Some nextidx -> 
Nat.Odd curidx -> 
Nat.Odd idx -> 
idx < nextidx -> 
idx = curidx \/ idx < curidx.
Proof.
intros.
unfold StateLib.Index.succ in *.
      destruct (lt_dec (curidx + 1) tableSize); try now contradict H.
      inversion H; clear H.
      destruct (lt_dec (iIndex + 1) tableSize); try now contradict H0.
      inversion H0; clear H0.
      destruct nextidx.
      inversion H4; clear H4.
      destruct iIndex.
      simpl in *.
      subst.
      inversion H5; clear H5.
      destruct curidx.
      simpl in *.
      destruct idx.
      simpl in *.
      rewrite <- H0 in H3.
      clear H0 Hi l0 l Hi0 .
      assert (i1 = i \/ i1 < i).
      unfold Nat.Odd in *.
      destruct H1 ; destruct H2.
      
      omega.
      destruct H.
      left.
      subst.
      f_equal.
      apply proof_irrelevance.
      right; trivial.
Qed.
      
Lemma indexSuccSuccEvenOr (curidx iIndex nextidx idx : index): 
StateLib.Index.succ curidx = Some iIndex ->
StateLib.Index.succ iIndex = Some nextidx -> 
Nat.Even curidx -> 
Nat.Even idx -> 
idx < nextidx -> 
idx = curidx \/ idx < curidx.
Proof.
intros.
unfold StateLib.Index.succ in *.
      destruct (lt_dec (curidx + 1) tableSize); try now contradict H.
      inversion H; clear H.
      destruct (lt_dec (iIndex + 1) tableSize); try now contradict H0.
      inversion H0; clear H0.
      destruct nextidx.
      inversion H4; clear H4.
      destruct iIndex.
      simpl in *.
      subst.
      inversion H5; clear H5.
      destruct curidx.
      simpl in *.
      destruct idx.
      simpl in *.
      rewrite <- H0 in H3.
      clear H0 Hi l0 l Hi0 .
      assert (i1 = i \/ i1 < i).
      destruct H1 ; destruct H2.
      omega.
      destruct H.
      left.
      subst.
      f_equal.
      apply proof_irrelevance.
      right; trivial.
Qed.

Lemma indexSuccSuccEvenOddLt (curidx iIndex nextidx idx : index): 
StateLib.Index.succ curidx = Some iIndex ->
StateLib.Index.succ iIndex = Some nextidx -> 
Nat.Even idx -> 
Nat.Odd curidx -> 
idx < nextidx -> 
idx < iIndex -> 
idx < curidx.
Proof.
intros.
unfold StateLib.Index.succ in *.
      destruct (lt_dec (curidx + 1) tableSize); try now contradict H.
      inversion H; clear H.
      destruct (lt_dec (iIndex + 1) tableSize); try now contradict H0.
      inversion H0; clear H0.
      destruct nextidx.
      inversion H5; clear H5.
      destruct iIndex.
      simpl in *.
      subst.
      inversion H6; clear H6.
      destruct curidx.
      simpl in *.
      destruct idx.
      simpl in *.
      destruct H1; destruct H2.
      subst.
      
      omega.
Qed.

Lemma indexNotEqSuccNotEq (idx1 idx2 : index): 
idx1 < tableSize -1 -> 
idx2 < tableSize -1 -> 
idx1 <> idx2 -> 
StateLib.Index.succ idx2 <> StateLib.Index.succ idx1.
Proof.
intros.
unfold Index.succ.
case_eq (lt_dec (idx2 + 1) tableSize); intros; try omega.  
case_eq (lt_dec (idx1 + 1) tableSize); intros; try omega.
destruct idx1; destruct idx2; simpl in *.
unfold not; intros Hfalse.
inversion Hfalse.
assert (i0 = i) by omega.
subst.
contradict H1.
f_equal.
apply proof_irrelevance.
Qed.

(** ADT : vaddr **)
Lemma lengthVAddrNotZero (va : vaddr) : fstLevel < (length va -1).
Proof. 
 unfold fstLevel.  destruct va.
 simpl. rewrite Hva. unfold CLevel. case_eq (lt_dec 0 nbLevel).
 simpl. intros. omega.
 intros. destruct level_d. simpl. omega. 
 Qed.

Lemma CLevelMinusEq0 : 
forall (a : level) b , CLevel (a -  b) = CLevel 0 ->   a = CLevel b \/ a < b. 
Proof.
intros.
unfold CLevel in *.  
case_eq (lt_dec (a - b) nbLevel );
intros lab Hab; rewrite Hab in *.
case_eq(lt_dec 0 nbLevel);
intros l0 H0;
rewrite H0 in*.
inversion H.
case_eq (lt_dec b nbLevel);
intros lb Hb.
simpl in *.
apply NPeano.Nat.sub_0_le in H2.
apply le_lt_or_eq in H2.
destruct H2. 
right; assumption.
left.
destruct a.
simpl in *.
subst.
assert (Hl =  ADT.CLevel_obligation_1 b lb ) by 
apply proof_irrelevance.
subst. reflexivity.
right; destruct a; simpl in *; omega.
assert (0 < nbLevel) by apply nbLevelNotZero.
now contradict H1.
destruct a. simpl in *.
omega.
Qed.

Lemma getNbLevelLe : 
forall nbL, 
Some nbL = StateLib.getNbLevel -> 
nbL <= CLevel (nbLevel - 1).
Proof.
intros.
unfold getNbLevel in *.
destruct (gt_dec nbLevel 0).
inversion H. 
unfold CLevel.
case_eq (lt_dec (nbLevel - 1) nbLevel); intros.
simpl.
omega.
omega.
assert (0 < nbLevel) by apply nbLevelNotZero.
omega.
Qed.

Lemma getNbLevelEq : 
forall nbL, 
Some nbL = StateLib.getNbLevel -> 
nbL = CLevel (nbLevel - 1).
Proof.
intros.
unfold getNbLevel in *.
destruct (gt_dec nbLevel 0).
inversion H.
destruct nbL.
simpl in *.
 
unfold CLevel.
case_eq (lt_dec (nbLevel - 1) nbLevel); intros.
inversion H.
subst.
f_equal.
apply proof_irrelevance.
assert (0 < nbLevel) by apply nbLevelNotZero.
omega.
now contradict H.
Qed.


(** beqPairs **)
Lemma beqPairsTrue : 
forall table1 idx1 table2 idx2 , table1 = table2 /\ idx1 = idx2 <->   
beqPairs (table1, idx1) (table2, idx2) beqPage beqIndex = true.
Proof.
intros.
unfold beqPairs.
cbn.  
unfold beqPage , beqIndex .
split.
* case_eq (table1 =? table2) ; case_eq(idx1 =? idx2);intuition.
  apply beq_nat_false in H.  
  destruct idx1 , idx2. simpl in *. inversion H3. omega.  
  apply beq_nat_false in H0.
  destruct table1, table2. simpl in *.
  inversion H2. omega.
  destruct ((false && false)%bool). trivial.
  apply beq_nat_false in H0.
  destruct table1, table2. simpl in *.
  inversion H2. omega.
* intros. 
  case_eq (table1 =? table2) ; case_eq(idx1 =? idx2);intuition.
  apply beq_nat_true in H1; trivial.
  destruct table1, table2; simpl in *; subst; f_equal; apply proof_irrelevance. 
  destruct idx1 , idx2; simpl in *.
  apply beq_nat_true in H0; subst; f_equal; apply proof_irrelevance.
  apply beq_nat_true in H1; trivial.
  destruct table1, table2; simpl in *; subst; f_equal; apply proof_irrelevance.
  rewrite H0 in H.
  rewrite H1 in H. 
  case_eq ((true && false)%bool); intros.
  apply Bool.andb_true_iff in H2.
  now contradict H2.
  rewrite H2 in H; now contradict H.
  rewrite H0 in H.
  rewrite H1 in H. 
  case_eq ((false && true)%bool); intros.
  apply Bool.andb_true_iff in H2.
  now contradict H2.
  rewrite H2 in H; now contradict H.
  apply beq_nat_true in H0.
  destruct idx1 , idx2; simpl in *;subst; f_equal; apply proof_irrelevance. 
  rewrite H0 in H.
  rewrite H1 in H. 
  case_eq ((false && false)%bool); intros.
  apply Bool.andb_true_iff in H2.
  now contradict H2.  
  rewrite H2 in H; now contradict H.
  rewrite H0 in H.
  rewrite H1 in H. 
  case_eq ((false && false)%bool); intros.
  apply Bool.andb_true_iff in H2.
  now contradict H2.  
  rewrite H2 in H; now contradict H.
Qed.

Lemma beqPairsFalse : 
forall table1 idx1 table2 idx2 , 
table1 <> table2 \/ idx1 <> idx2 <-> 
beqPairs (table1, idx1) (table2, idx2) beqPage beqIndex = false.
Proof.
intros.
unfold beqPairs.
cbn.  
unfold beqPage , beqIndex .
intuition.
case_eq (table1 =? table2) ; case_eq(idx1 =? idx2);intuition.
contradict H0.
apply beq_nat_true in H1.
destruct table1, table2. simpl in *. subst.
assert (Hp = Hp0).
apply proof_irrelevance. subst. trivial. 
admit.
admit. (*   

contradict H2.
apply beq_nat_true in H0.
destruct idx1, idx2. simpl in *. subst.
assert (Hi = Hi0).
apply proof_irrelevance. subst. trivial. *)
Admitted.