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
    This file contains required lemmas to prove that updating the first shadow 
    structure preserves isolation and consistency properties  *)

Require Import Model.ADT Core.Internal Isolation Consistency WeakestPreconditions 
Invariants StateLib Model.Hardware  Model.MAL 
DependentTypeLemmas Model.Lib InternalLemmas PropagatedProperties.
Require Import Coq.Logic.ProofIrrelevance Omega List Bool. 

Lemma getPdAddDerivation partition (descChild : vaddr) 
table idx (s : state) entry :
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->  
StateLib.getPd partition
  (memory
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |}) =
StateLib.getPd partition (memory s).
Proof.
intros Hentry.
unfold StateLib.getPd.
case_eq ( StateLib.Index.succ PDidx ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn. 
case_eq (beqPairs (table, idx) (partition, i) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  partition i (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  partition i   (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. reflexivity.
Qed.

Lemma getFstShadowAddDerivation partition (descChild : vaddr) 
table idx (s : state) entry :
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->  
StateLib.getFstShadow partition
  (memory
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |}) =
StateLib.getFstShadow partition (memory s).
Proof.
intros Hentry.
unfold StateLib.getFstShadow.
case_eq ( StateLib.Index.succ sh1idx ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn. 
case_eq (beqPairs (table, idx) (partition, i) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  partition i (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  partition i   (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. reflexivity.
Qed.

Lemma getIndirectionAddDerivation sh1 table idx descChild s entry va nbL stop:
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->
getIndirection sh1 va nbL stop
  {|  currentPartition := currentPartition s;
      memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |} =
getIndirection sh1 va nbL stop s .
Proof.
intros Hentry.
revert sh1 nbL.
induction  stop.
+ simpl. trivial.
+ simpl. intros. 
  destruct (StateLib.Level.eqb nbL fstLevel);trivial.
  set (entry0 := (VE {| pd := false; va := descChild |})  ) in *.
  simpl.
  assert ( StateLib.readPhyEntry sh1 (StateLib.getIndexOfAddr va nbL)
                  (add table idx entry0 (memory s) beqPage beqIndex) = 
           StateLib.readPhyEntry sh1 (StateLib.getIndexOfAddr va nbL) (memory s)) as HreadPhyEnt.
  { unfold StateLib.readPhyEntry.
    cbn.  
    case_eq ( beqPairs (table, idx) (sh1, StateLib.getIndexOfAddr va nbL) beqPage beqIndex);trivial;intros Hpairs.
    + apply beqPairsTrue in Hpairs.
      destruct Hpairs as (Htable & Hidx).  subst.
      rewrite Hentry. 
      cbn. trivial.
    + apply beqPairsFalse in Hpairs.
      assert (lookup sh1 (StateLib.getIndexOfAddr va nbL)
                 (removeDup table idx (memory s) beqPage beqIndex) beqPage beqIndex = 
              lookup sh1 (StateLib.getIndexOfAddr va nbL) (memory s) beqPage beqIndex) as Hmemory.
        { apply removeDupIdentity. subst.  intuition. }
      rewrite Hmemory. reflexivity.
   } 
  rewrite HreadPhyEnt.
  destruct (StateLib.readPhyEntry sh1 (StateLib.getIndexOfAddr va nbL) (memory s) );trivial.
  destruct (defaultPage =? p);trivial.
  destruct ( StateLib.Level.pred nbL );trivial.
Qed.

Lemma readPDflagAddDerivation table1 table2 idx1 idx2 newEntry s: 
table1 <> table2 \/ idx1 <> idx2 -> 
StateLib.readPDflag table1 idx1
  (add table2 idx2 (VE newEntry) (memory s) beqPage beqIndex) =
StateLib.readPDflag table1 idx1(memory s).
Proof.     
intros Hnoteq.
unfold StateLib.readPDflag. cbn. 
case_eq ( beqPairs (table2, idx2) (table1, idx1) beqPage beqIndex);intros Hpairs.
+ apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidx).
   contradict Hnoteq. intuition.
+ intros.
  apply beqPairsFalse in Hpairs.
  assert (lookup table1 idx1 (removeDup table2 idx2 (memory s) beqPage beqIndex) beqPage beqIndex
   = lookup table1 idx1 (memory s) beqPage beqIndex) as Hmemory.
  { apply removeDupIdentity. intuition. }
  rewrite Hmemory. reflexivity.
Qed. 

Lemma checkChildAddDerivation (descChild : vaddr) 
table idx (s : state) partition nbL va entry : 
StateLib.readPDflag table idx (memory s) = Some false -> 
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->  
checkChild partition nbL
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |} va =
checkChild partition nbL s va.
Proof.
intros  Hreadpdflag Hentry.
unfold checkChild.
set (s' :=  {| currentPartition := currentPartition s;
               memory := add table idx (VE {| pd := false; va := descChild |}) 
                            (memory s) beqPage beqIndex |}) in *.
assert( StateLib.getFstShadow partition (memory s')= StateLib.getFstShadow partition (memory s) ) as Hfstsh.
{ apply getFstShadowAddDerivation with entry;trivial. }
rewrite Hfstsh.
case_eq(getFstShadow partition (memory s));trivial.
intros sh1 Hsh1.
assert (getIndirection sh1 va nbL (nbLevel - 1)  s' = 
          getIndirection sh1 va nbL (nbLevel - 1)  s) as Hindeq.
{ apply getIndirectionAddDerivation with entry;trivial. }
rewrite Hindeq.
case_eq (getIndirection sh1 va nbL (nbLevel - 1) s);trivial.
intros sh1LastEntry Hsh1LastEntry.
case_eq (sh1LastEntry =? defaultPage) ; intros; trivial.
assert (StateLib.readPDflag sh1LastEntry (StateLib.getIndexOfAddr va fstLevel) (memory s')  = 
        StateLib.readPDflag sh1LastEntry (StateLib.getIndexOfAddr va fstLevel) (memory s)) as Hpdflag. 
{ unfold s';cbn.
  unfold StateLib.readPDflag in *.
  cbn.
  case_eq(beqPairs (table, idx) (sh1LastEntry, StateLib.getIndexOfAddr va fstLevel)
         beqPage beqIndex); intros; cbn.
  + apply beqPairsTrue in H0.
    destruct H0.
    subst.
    symmetry; assumption.
  + apply beqPairsFalse in H0.
    assert(Hmemory: lookup sh1LastEntry (StateLib.getIndexOfAddr va fstLevel)
                   (removeDup table idx (memory s) beqPage beqIndex)beqPage beqIndex = 
                   lookup sh1LastEntry (StateLib.getIndexOfAddr va fstLevel) (memory s) 
                   beqPage beqIndex ).
    { apply removeDupIdentity;intuition. }
    rewrite Hmemory;trivial. }
rewrite Hpdflag.
reflexivity. 
Qed.

Lemma getPdsVAddrAddDerivation (descChild : vaddr) 
table idx (s : state) partition nbL entry :
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->  
StateLib.readPDflag table idx (memory s) = Some false -> 
getPdsVAddr partition nbL getAllVAddr
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |})
   (memory s) beqPage beqIndex |} =
getPdsVAddr partition nbL getAllVAddr s.
Proof.
unfold getPdsVAddr.
induction getAllVAddr.
simpl; trivial.
intros.
simpl. 
set (s' :=  {|
    currentPartition := currentPartition s;
    memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |}) in *.
assert (StateLib.checkChild partition nbL s' a =
        StateLib.checkChild partition nbL s a) as HpartRef.
unfold s'.

apply checkChildAddDerivation with entry ;trivial; trivial.
rewrite HpartRef.
rewrite IHl; trivial.
Qed.  

Lemma getMappedPagesAuxAddDerivation (descChild : vaddr) 
table idx (s : state) partition nbL pd : 
getMappedPagesAux pd (getPdsVAddr partition nbL getAllVAddr s)
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) 
              (memory s) beqPage beqIndex |} =
getMappedPagesAux pd (getPdsVAddr partition nbL getAllVAddr s) s.
Proof.
Admitted.

Lemma getChildrenAddDerivation partition (descChild : vaddr) 
table idx entry (s : state):
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->  
StateLib.readPDflag table idx (memory s) = Some false -> 
getChildren partition
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) 
              (memory s) beqPage beqIndex |} = getChildren partition s.
Proof.
intros Hentry Hreadpdflag.
unfold getChildren.
set (entry0 := (VE {| pd := false; va := descChild |}) ) in *. 
set (s' :={| currentPartition := currentPartition s;
             memory := add table idx entry0 (memory s) beqPage beqIndex |}) in *.
destruct StateLib.getNbLevel;trivial.
assert(StateLib.getPd partition (memory s') =
         StateLib.getPd partition (memory s)) as HgetPd.
         unfold s'.
apply getPdAddDerivation with entry;trivial.
rewrite HgetPd.
destruct (StateLib.getPd partition (memory s));trivial.
assert (getPdsVAddr partition l getAllVAddr s' = 
            getPdsVAddr partition l getAllVAddr s) as HgetPdsVa.
            unfold s'.
 { apply getPdsVAddrAddDerivation with entry;trivial. }
rewrite HgetPdsVa.
unfold s' , entry0.
apply getMappedPagesAuxAddDerivation;trivial.
Qed.

Lemma getPartitionAuxAddDerivation partition (descChild : vaddr) 
table idx entry (s : state):
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->  
StateLib.readPDflag table idx (memory s) = Some false -> 
getPartitionAux partition 
    {| currentPartition := currentPartition s;
       memory := add table idx (VE {| pd := false; va := descChild |}) 
                      (memory s) beqPage beqIndex |} (nbPage+1) =
getPartitionAux partition s (nbPage+1). 
Proof.
intros Hentry Hreadpdflag.
revert partition.
induction (nbPage+1).
now cbn.
simpl.
set (s' :=   {| currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) 
                      (memory s) beqPage beqIndex |}) in *.
intros. f_equal.
assert (getChildren partition s = getChildren partition s') as Hchildren.
unfold s'. symmetry.
apply getChildrenAddDerivation with entry;trivial. 
rewrite <- Hchildren.
simpl.
clear Hchildren.
induction  (getChildren partition s).
 simpl. trivial.
 simpl.
 f_equal.
 apply IHn.
 apply IHl.
Qed.

Lemma getPartitionsAddDerivation (descChild : vaddr) table idx entry (s : state):
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->  
StateLib.readPDflag table idx (memory s) = Some false -> 
getPartitions multiplexer
          {|
          currentPartition := currentPartition s;
          memory := add table idx (VE {| pd := false; va := descChild |}) 
                      (memory s) beqPage beqIndex |} =
getPartitions multiplexer s.
Proof.
intros Hentry Hreadpdflag.
unfold getPartitions.
apply getPartitionAuxAddDerivation with entry;trivial.
Qed.

Lemma partitionsIsolationUpdtateSh1Structure (descChild : vaddr) table idx entry (s : state):
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
StateLib.readPDflag table idx (memory s) = Some false ->  
partitionsIsolation s -> 
partitionsIsolation
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) 
              (memory s) beqPage beqIndex |}.
Proof.
intros.
unfold partitionsIsolation in *.
Admitted.