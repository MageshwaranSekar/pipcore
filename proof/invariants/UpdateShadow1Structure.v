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
  (add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex) =
StateLib.getPd partition (memory s).
Proof.
simpl.
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
getFstShadow partition
  (add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex) =
getFstShadow partition (memory s).
Proof.
simpl.
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

Lemma getSndShadowAddDerivation child (descChild : vaddr) 
table idx (s : state) entry :
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->  
getSndShadow child
  (add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex) =
getSndShadow child (memory s).
Proof.
intros Hentry.
unfold StateLib.getSndShadow.
case_eq ( StateLib.Index.succ sh2idx ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn. 
case_eq (beqPairs (table, idx) (child, i) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  child i (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  child i   (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. reflexivity.
Qed.

Lemma getParentAddDerivation partition (descChild : vaddr) 
table idx (s : state) entry :
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->
StateLib.getParent partition
  (add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex) =
StateLib.getParent partition (memory s).
Proof.
simpl.
intros Hentry.
unfold StateLib.getParent.
case_eq ( StateLib.Index.succ PPRidx ); intros; trivial.
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

Lemma getConfigTablesLinkedListAddDerivation child (descChild : vaddr) 
table idx (s : state) entry :
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->  
getConfigTablesLinkedList child
  (add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex) =
getConfigTablesLinkedList child (memory s).
Proof.
intros Hentry.
unfold StateLib.getConfigTablesLinkedList.
case_eq ( StateLib.Index.succ sh3idx ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn. 
case_eq (beqPairs (table, idx) (child, i) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  child i (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  child i   (memory s) beqPage beqIndex) as Hmemory.
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
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) ->
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
    destruct Hreadpdflag.
    
    symmetry; assumption.
    rewrite Hentry in H0.
    now contradict H0.
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
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) ->
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
Lemma readPresentAddDerivation (descChild : vaddr) 
table idx (s : state)  p idx2  entry: 
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->  
 StateLib.readPresent p idx2
    (add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex) =
     StateLib.readPresent p idx2 (memory s).
Proof.
intros Hentry.
unfold StateLib.readPresent.
cbn.
case_eq( beqPairs (table, idx) (p, idx2) beqPage beqIndex); intros.
apply beqPairsTrue in H.
destruct H; subst.
rewrite Hentry; trivial.
apply beqPairsFalse in H.
assert(Hmemory : lookup p idx2 (removeDup table idx (memory s) beqPage beqIndex) beqPage beqIndex = 
 lookup p idx2 (memory s) beqPage beqIndex ); intros.
 { apply removeDupIdentity ; intuition. }
 rewrite Hmemory; reflexivity. 
Qed.

Lemma readAccessibleAddDerivation (descChild : vaddr) 
table idx (s : state)  p idx2  entry: 
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->  
 StateLib.readAccessible p idx2
    (add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex) =
     StateLib.readAccessible p idx2 (memory s).
Proof.
intros Hentry.
unfold StateLib.readAccessible.
cbn.
case_eq( beqPairs (table, idx) (p, idx2) beqPage beqIndex); intros.
apply beqPairsTrue in H.
destruct H; subst.
rewrite Hentry; trivial.
apply beqPairsFalse in H.
assert(Hmemory : lookup p idx2 (removeDup table idx (memory s) beqPage beqIndex) beqPage beqIndex = 
 lookup p idx2 (memory s) beqPage beqIndex ); intros.
 { apply removeDupIdentity ; intuition. }
 rewrite Hmemory; reflexivity. 
Qed.

Lemma readPhyEntryAddDerivation (descChild : vaddr) 
table idx (s : state)  p idx2  entry: 
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->  
StateLib.readPhyEntry p idx2
  (add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex) =
StateLib.readPhyEntry p idx2 (memory s).
Proof.
intros Hentry.
unfold StateLib.readPhyEntry.
cbn.
case_eq( beqPairs (table, idx) (p, idx2) beqPage beqIndex); intros.
apply beqPairsTrue in H.
destruct H; subst.
rewrite Hentry; trivial.
apply beqPairsFalse in H.
assert(Hmemory : lookup p idx2 (removeDup table idx (memory s) beqPage beqIndex) beqPage beqIndex = 
 lookup p idx2 (memory s) beqPage beqIndex ); intros.
 { apply removeDupIdentity ; intuition. }
rewrite Hmemory; reflexivity.
Qed.

Lemma readPhysicalAddDerivation (descChild : vaddr) 
table idx (s : state)  p idx2  entry: 
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->  
StateLib.readPhysical p idx2
  (add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex) =
StateLib.readPhysical p idx2 (memory s).
Proof.
intros Hentry.
unfold StateLib.readPhysical.
cbn.
case_eq( beqPairs (table, idx) (p, idx2) beqPage beqIndex); intros.
apply beqPairsTrue in H.
destruct H; subst.
rewrite Hentry; trivial.
apply beqPairsFalse in H.
assert(Hmemory : lookup p idx2 (removeDup table idx (memory s) beqPage beqIndex) beqPage beqIndex = 
 lookup p idx2 (memory s) beqPage beqIndex ); intros.
 { apply removeDupIdentity ; intuition. }
rewrite Hmemory; reflexivity.
Qed.

Lemma readVirtualAddDerivation (descChild : vaddr) 
table idx (s : state)  p idx2  entry: 
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->  
StateLib.readVirtual p idx2
  (add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex) =
StateLib.readVirtual p idx2 (memory s).
Proof.
intros Hentry.
unfold StateLib.readVirtual.
cbn.
case_eq( beqPairs (table, idx) (p, idx2) beqPage beqIndex); intros.
apply beqPairsTrue in H.
destruct H; subst.
rewrite Hentry; trivial.
apply beqPairsFalse in H.
assert(Hmemory : lookup p idx2 (removeDup table idx (memory s) beqPage beqIndex) beqPage beqIndex = 
 lookup p idx2 (memory s) beqPage beqIndex ); intros.
 { apply removeDupIdentity ; intuition. }
rewrite Hmemory; reflexivity.
Qed.

Lemma readIndexAddDerivation (descChild : vaddr) 
table idx (s : state)  p idx2  entry: 
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->  
StateLib.readIndex p idx2
  (add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex) =
StateLib.readIndex p idx2 (memory s).
Proof.
intros Hentry.
unfold StateLib.readIndex.
cbn.
case_eq( beqPairs (table, idx) (p, idx2) beqPage beqIndex); intros.
apply beqPairsTrue in H.
destruct H; subst.
rewrite Hentry; trivial.
apply beqPairsFalse in H.
assert(Hmemory : lookup p idx2 (removeDup table idx (memory s) beqPage beqIndex) beqPage beqIndex = 
 lookup p idx2 (memory s) beqPage beqIndex ); intros.
 { apply removeDupIdentity ; intuition. }
rewrite Hmemory; reflexivity.
Qed.

Lemma  getMappedPageAddDerivation (descChild : vaddr) 
table idx (s : state)  va pd entry: 
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->  
getMappedPage pd
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |} va =
getMappedPage pd s va.
Proof.
intros Hentry.
unfold getMappedPage.
destruct( StateLib.getNbLevel ); intros; trivial.
cbn.
assert(Hind : getIndirection pd va l (nbLevel - 1)
    {|
    currentPartition := currentPartition s;
    memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |} =
    getIndirection pd va l (nbLevel - 1) s).
apply getIndirectionAddDerivation with entry; trivial.
rewrite Hind.  
destruct(getIndirection pd va l (nbLevel - 1) s); intros; trivial.
destruct(defaultPage =? p);trivial.
 assert(Hpresent :   StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel)
    (add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex) =
     StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel) (memory s)).
apply readPresentAddDerivation with entry; trivial.
rewrite Hpresent.
destruct(StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel) (memory s) ); trivial.
destruct b; trivial.
apply readPhyEntryAddDerivation with entry; trivial .
Qed.

Lemma getMappedPagesAuxAddDerivation (descChild : vaddr) 
table idx (s : state)  listVa pd entry: 
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->  
getMappedPagesAux pd listVa
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) 
              (memory s) beqPage beqIndex |} =
getMappedPagesAux pd listVa s.
Proof.
unfold getMappedPagesAux.
intros Hentry. 
f_equal.
unfold  getMappedPagesOption.
induction listVa.
simpl. trivial.
simpl.
rewrite IHlistVa.
f_equal. 
apply getMappedPageAddDerivation with entry; trivial.
Qed.

Lemma getMappedPagesAddDerivation child (descChild : vaddr) 
table idx (s : state)  entry: 
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->  
getMappedPages child
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |} =
getMappedPages child s.
Proof.
intros Hentry.
unfold getMappedPages.
assert(Hpd :  StateLib.getPd child
    (memory
       {|
       currentPartition := currentPartition s;
       memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |}) =
       StateLib.getPd child (memory s)).
apply getPdAddDerivation with entry; trivial.
rewrite Hpd.
destruct (StateLib.getPd child (memory s)); trivial.
apply getMappedPagesAuxAddDerivation with entry;trivial.
Qed.

Lemma getChildrenAddDerivation partition (descChild : vaddr) 
table idx entry (s : state):
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->  
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) ->
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
apply getMappedPagesAuxAddDerivation with entry;trivial.
Qed.

Lemma getPartitionAuxAddDerivation partition (descChild : vaddr) 
table idx entry (s : state):
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->  
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) ->
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
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) -> 
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

Lemma getTablePagesAddDerivation   (descChild : vaddr) table idx entry size p (s : state):
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
getTablePages p size
 {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |}=
getTablePages p size s.
Proof.
revert p .
set (s' :=   {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |}).
induction size;
intros;  trivial.
simpl.
case_eq(beqPairs (table, idx) (p, CIndex size) beqPage beqIndex);intros Hpairs.
+ apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidx).
  subst.
  rewrite H.
  apply IHsize;trivial.
+ apply beqPairsFalse in Hpairs.
  assert (lookup   p (CIndex size) (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  p (CIndex size) (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. subst.  intuition. }
  rewrite  Hmemory. 
  destruct (lookup p (CIndex size) (memory s) beqPage beqIndex); 
  [ |apply IHsize; trivial].
  destruct v; try apply IHsize; trivial.
  apply IHsize with p in H.
  rewrite H.
  reflexivity.
Qed.

Lemma getIndirectionsAddDerivation  (descChild : vaddr) table idx entry pd (s : state):
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->  
getIndirections pd
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |} =
getIndirections pd s.
Proof.
intros Hentry.
unfold getIndirections.
revert pd.
induction nbLevel.
simpl. trivial. simpl.
intros. f_equal.
    assert (getTablePages pd tableSize   {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |} = getTablePages pd tableSize s) as Htablepages.
apply getTablePagesAddDerivation with entry ;trivial.
rewrite Htablepages.
clear Htablepages.
induction (getTablePages pd tableSize s); intros; trivial.
simpl in *.
rewrite IHn. 
f_equal.
apply IHl.
Qed.

Lemma getConfigTablesLinkedListsAddDerivation sh3  (descChild : vaddr) table idx entry (s : state):
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
getTrdShadows sh3
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |} nbPage =
getTrdShadows sh3 s nbPage.
Proof.
revert sh3.
induction nbPage;trivial.
intros. simpl.
 set (s' :=   {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |} ) in *.
destruct (StateLib.getMaxIndex);trivial.
assert(HreadPhyEnt :  StateLib.readPhyEntry sh3 i
    (add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex) = 
    StateLib.readPhyEntry sh3 i (memory s) ).
apply readPhyEntryAddDerivation with entry;trivial.
rewrite HreadPhyEnt.
destruct (StateLib.readPhyEntry sh3 i (memory s));trivial.
destruct (p =? defaultPage) ;trivial.
f_equal.
apply IHn; trivial.
Qed. 

Lemma getConfigPagesAuxAddDerivation child (descChild : vaddr) table idx entry (s : state):
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
getConfigPagesAux child
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |} =
getConfigPagesAux child s.
Proof.
intros Hentry.
unfold getConfigPagesAux.
cbn.

assert (StateLib.getPd child  (add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex) = StateLib.getPd child (memory s) ) as HgetPd.
apply getPdAddDerivation with entry ;trivial.
unfold getConfigPagesAux in *.
rewrite HgetPd.
destruct (StateLib.getPd child (memory s)) as [ pd|] ;trivial.
assert (StateLib.getFstShadow child  (add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex) = StateLib.getFstShadow child (memory s)) as Hsh1.
apply getFstShadowAddDerivation with entry ;trivial.
rewrite Hsh1.
destruct  (StateLib.getFstShadow child (memory s))as [ sh1|]  ;trivial.
assert (StateLib.getSndShadow child  (add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex) = StateLib.getSndShadow child (memory s)) as Hsh2.
apply getSndShadowAddDerivation with entry ;trivial.
rewrite Hsh2.
destruct  (StateLib.getSndShadow child (memory s))as [ sh2|]  ;trivial.
assert (StateLib.getConfigTablesLinkedList child   (add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex)= StateLib.getConfigTablesLinkedList child (memory s)) as Hsh3.
apply getConfigTablesLinkedListAddDerivation with entry; trivial.
rewrite Hsh3.
destruct  (StateLib.getConfigTablesLinkedList child (memory s)) as [ sh3|] ;trivial.
assert (getIndirections pd   {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |}  = getIndirections pd s) as Hind.
apply getIndirectionsAddDerivation with entry ; trivial.
rewrite Hind; clear Hind.
assert (forall sh1, getIndirections sh1  {|
        currentPartition := currentPartition s;
        memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |} = getIndirections sh1 s) as Hind.
intros. 
apply getIndirectionsAddDerivation with entry; trivial.
rewrite Hind.
rewrite Hind.
do 7 f_equal.
apply getConfigTablesLinkedListsAddDerivation with entry; trivial.
Qed.

Lemma getConfigPagesAddDerivation child (descChild : vaddr) table idx entry (s : state):
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
getConfigPages child
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |} =
getConfigPages child s.
Proof.
intros Hentry.
unfold getConfigPages; f_equal.
apply getConfigPagesAuxAddDerivation with entry; trivial.
Qed.

Lemma getUsedPagesAddDerivation child (descChild : vaddr) table idx entry (s : state):
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
getUsedPages child
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |} =
getUsedPages child s.
Proof.
intros Hentry.
unfold getUsedPages.
f_equal.
apply getConfigPagesAddDerivation with entry; trivial.
apply getMappedPagesAddDerivation with entry; trivial.
Qed.

Lemma partitionsIsolationUpdtateSh1Structure (descChild : vaddr) table idx entry (s : state):
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None )->  
partitionsIsolation s -> 
partitionsIsolation
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) 
              (memory s) beqPage beqIndex |}.
Proof.
intros.
unfold partitionsIsolation in *.
assert(Hpartitions : getPartitions multiplexer
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |} = 
getPartitions multiplexer s).
apply getPartitionsAddDerivation with entry; trivial.
rewrite Hpartitions.
intros.
assert(Hchildren :getChildren parent
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |} =
     getChildren parent s) .
apply getChildrenAddDerivation with entry; trivial.
rewrite Hchildren in *.
clear Hchildren.
assert(Husedpages : forall child,  getUsedPages child
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |} = 
getUsedPages child s).
intros.
apply getUsedPagesAddDerivation with entry; trivial.
rewrite Husedpages.
rewrite Husedpages.
apply H1 with parent; trivial.
Qed.
Lemma getAccessibleMappedPageAddDerivation pd (descChild : vaddr) table idx entry va (s : state):
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
getAccessibleMappedPage pd
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |} va =
getAccessibleMappedPage pd s va.
Proof.
intros Hentry.
set(s' :=  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |} ).
  
unfold getAccessibleMappedPage.
destruct( StateLib.getNbLevel ); intros; trivial.
cbn.
assert(Hind : getIndirection pd va l (nbLevel - 1)
    {|
    currentPartition := currentPartition s;
    memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |} =
    getIndirection pd va l (nbLevel - 1) s).
apply getIndirectionAddDerivation with entry; trivial.
unfold s'.
rewrite Hind.  
destruct(getIndirection pd va l (nbLevel - 1) s); intros; trivial.
destruct(defaultPage =? p);trivial.
 assert(Hpresent :   StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel)
    (add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex) =
     StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel) (memory s)).
apply readPresentAddDerivation with entry; trivial.
rewrite Hpresent.
destruct(StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel) (memory s) ); trivial.
destruct b; trivial.
assert( Hacc : StateLib.readAccessible p (StateLib.getIndexOfAddr va fstLevel)
    (add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex) = 
    StateLib.readAccessible p (StateLib.getIndexOfAddr va fstLevel) (memory s) ).
apply readAccessibleAddDerivation with entry;trivial.
rewrite Hacc.
destruct (StateLib.readAccessible p (StateLib.getIndexOfAddr va fstLevel) (memory s) ); trivial.
destruct b; trivial.
apply readPhyEntryAddDerivation with entry; trivial .
Qed.

Lemma getAccessibleMappedPagesAuxAddDerivation  (descChild : vaddr) table idx entry pd (s : state):
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
getAccessibleMappedPagesAux pd getAllVAddr
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |} =
getAccessibleMappedPagesAux pd getAllVAddr s.
Proof.
unfold getAccessibleMappedPagesAux.
intros Hentry.
unfold  getAccessibleMappedPagesOption.
f_equal.
revert pd.
induction getAllVAddr; simpl; trivial.
intros.
set(s' :=  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |} ).
f_equal.
apply getAccessibleMappedPageAddDerivation with entry;trivial.
apply IHl.
Qed.

Lemma getAccessibleMappedPagesAddDerivation partition (descChild : vaddr) table idx entry (s : state):
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
getAccessibleMappedPages partition
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |} =
getAccessibleMappedPages partition s.
Proof.
intros Hentry.
unfold getAccessibleMappedPages.
assert(HgetPd : StateLib.getPd partition
    (add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex) =
StateLib.getPd partition (memory s) ).
apply getPdAddDerivation with entry; trivial.
simpl.
rewrite HgetPd.
case_eq(StateLib.getPd partition (memory s) ); intros;trivial.
apply getAccessibleMappedPagesAuxAddDerivation with entry; trivial.
Qed.

Lemma  kernelDataIsolationUpdtateSh1Structure (descChild : vaddr) table idx entry (s : state):
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) ->
 kernelDataIsolation s -> 
 kernelDataIsolation 
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) 
              (memory s) beqPage beqIndex |}.
Proof.
unfold kernelDataIsolation.
intros.
assert(Hconfig : getConfigPages partition2  {|
                         currentPartition := currentPartition s;
                         memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |} =
                     getConfigPages partition2 s ).
apply getConfigPagesAddDerivation with entry;trivial.
rewrite Hconfig.
assert(Hpartitions : getPartitions multiplexer
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |} = 
getPartitions multiplexer s).
apply getPartitionsAddDerivation with entry; trivial.
rewrite Hpartitions in *.
clear Hconfig Hpartitions.
assert(getAccessibleMappedPages partition1
             {| currentPartition := currentPartition s;
                memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |} = 
         getAccessibleMappedPages partition1 s).
apply getAccessibleMappedPagesAddDerivation with entry; trivial.
rewrite H4.
apply H1; trivial.
Qed.

Lemma verticalSharingUpdtateSh1Structure (descChild : vaddr) table idx entry (s : state):
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) -> 
verticalSharing s -> 
verticalSharing
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) 
              (memory s) beqPage beqIndex |}.
Proof.
unfold verticalSharing.
intros.
assert(Hpartitions : getPartitions multiplexer
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) 
                  (memory s) beqPage beqIndex |} = 
getPartitions multiplexer s).
apply getPartitionsAddDerivation with entry; trivial.
rewrite Hpartitions in *; clear Hpartitions.
assert(Hchildren : getChildren parent
          {|
          currentPartition := currentPartition s;
          memory := add table idx (VE {| pd := false; va := descChild |}) 
                      (memory s) beqPage beqIndex |} = 
         getChildren parent s).
apply getChildrenAddDerivation with entry;trivial.
rewrite Hchildren in *; clear Hchildren.
assert(Hused : getUsedPages child
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) 
                 (memory s) beqPage beqIndex |} =
       getUsedPages child s).
apply getUsedPagesAddDerivation with entry; trivial.
rewrite Hused in *; clear Hused.
assert (Hmapped : getMappedPages parent
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) 
                 (memory s) beqPage beqIndex |}=
         getMappedPages parent s).
apply getMappedPagesAddDerivation with entry;trivial.
rewrite Hmapped;clear Hmapped.
apply H1;trivial.
Qed.

Lemma isVAAddDerivation idx partition table descChild entry idxroot s:
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->
isVA partition idxroot s -> 
isVA partition idxroot
  {| currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) 
     (memory s) beqPage beqIndex |}.
Proof.
intros Hentry.
unfold isVA.
cbn.
case_eq (beqPairs (table, idx) (partition, idxroot) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  partition idxroot (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  partition idxroot   (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.

Lemma isPEAddDerivation idx partition table descChild entry idxroot s:
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->
isPE partition idxroot s -> 
isPE partition idxroot
  {| currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) 
     (memory s) beqPage beqIndex |}.
Proof.
intros Hentry.
unfold isPE.
cbn.
case_eq (beqPairs (table, idx) (partition, idxroot) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  partition idxroot (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  partition idxroot   (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.

Lemma isVEAddDerivation idx partition table descChild entry idxroot s:
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->
isVE partition idxroot s -> 
isVE partition idxroot
  {| currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) 
     (memory s) beqPage beqIndex |}.
Proof.
intros Hentry.
unfold isVE.
cbn.
case_eq (beqPairs (table, idx) (partition, idxroot) beqPage beqIndex);trivial;intros Hpairs.
apply beqPairsFalse in Hpairs.
   assert (lookup  partition idxroot (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  partition idxroot   (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.

Lemma nextEntryIsPPAddDerivation idx partition table descChild entry idxroot PPentry s:
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->
nextEntryIsPP partition idxroot PPentry s <-> 
nextEntryIsPP partition idxroot PPentry
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |}.
Proof.
split;intros Hentry;
unfold nextEntryIsPP in *;
cbn;
destruct ( StateLib.Index.succ idxroot); trivial.
- case_eq (beqPairs (table, idx) (partition, i) beqPage beqIndex);trivial;intros Hpairs.
   + apply beqPairsTrue in Hpairs.
     destruct Hpairs as (Htable & Hidx).  subst.      
     rewrite H in *.
     trivial.
   + apply beqPairsFalse in Hpairs.
     assert (lookup  partition i (removeDup table idx (memory s) beqPage beqIndex)
             beqPage beqIndex = lookup  partition i   (memory s) beqPage beqIndex) as Hmemory.
     { apply removeDupIdentity. intuition. }
       rewrite Hmemory. trivial.
- cbn in *.
  case_eq (beqPairs (table, idx) (partition, i) beqPage beqIndex);trivial;intros Hpairs.
  + rewrite Hpairs in *; now contradict Hentry.
  + rewrite Hpairs in *.
    assert (lookup  partition i (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  partition i   (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity.  apply beqPairsFalse in Hpairs. intuition. }
     rewrite Hmemory in *. trivial.     
Qed. 

Lemma partitionDescriptorEntryAddDerivation idx table descChild entry s:
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) -> 
partitionDescriptorEntry s -> 
partitionDescriptorEntry
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |}  .
Proof.
intros Hentry Hpdflag.
unfold partitionDescriptorEntry.
intros.
assert(Hpartitions : getPartitions multiplexer
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) 
                  (memory s) beqPage beqIndex |} = 
getPartitions multiplexer s).
apply getPartitionsAddDerivation with entry; trivial.
rewrite Hpartitions in *; clear Hpartitions.
assert(Hpde : idxroot < tableSize - 1 /\
              isVA partition idxroot s /\
              (exists entry : page, nextEntryIsPP partition idxroot entry s /\ 
                                    entry <> defaultPage)).
apply H; trivial.
destruct Hpde as (Hidxlt & Hva & Hpp).
split; trivial.
split.
apply isVAAddDerivation with entry; trivial.
destruct Hpp as (PPentry & Hpp & Hnotnull).
exists PPentry; split;trivial.
apply nextEntryIsPPAddDerivation with entry; trivial.
Qed.

Lemma dataStructurePdSh1Sh2asRootAddDerivation descChild idxroot s table idx entry :
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) ->
dataStructurePdSh1Sh2asRoot idxroot s ->
dataStructurePdSh1Sh2asRoot  idxroot
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hentry Hpdflag Hds.
unfold dataStructurePdSh1Sh2asRoot in *.
assert(Hpartitions : getPartitions multiplexer
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) 
                  (memory s) beqPage beqIndex |} = 
getPartitions multiplexer s).
apply getPartitionsAddDerivation with entry; trivial.
rewrite Hpartitions in *; clear Hpartitions.
intros.
rewrite <- nextEntryIsPPAddDerivation in H0; try eassumption.
assert (Hind : getIndirection entry0 va level stop s = Some indirection).
{ rewrite <- H3. symmetry.
  apply getIndirectionAddDerivation with entry; trivial. }
clear H3.
assert(Hdss :indirection = defaultPage \/
      (stop < level /\ isPE indirection idx0 s \/
       stop = level /\
       (isVE indirection idx0 s /\ idxroot = sh1idx \/
        isVA indirection idx0 s /\ idxroot = sh2idx \/ isPE indirection idx0 s /\ idxroot = PDidx)) /\
      indirection <> defaultPage).
apply Hds with partition entry0 va; trivial.
clear Hds.
destruct Hdss as [Hds | Hds];[left;trivial|].
right.
destruct Hds as (Hds & Hnotnull); split; trivial.
destruct Hds as [(Hlt & Hpe) | Hds].
+ left; split; trivial.
  apply isPEAddDerivation with entry; trivial.
+ right.
  destruct Hds as (Hlevel & [(Hve & Hidx) | [(Hva & Hidx) | (Hpe & Hidx)]]).
  split; trivial.
  - left; split; trivial.
    apply isVEAddDerivation with entry; trivial.
  - split; trivial.
    right; left;split; trivial.
    apply isVAAddDerivation with entry; trivial.
  - split;trivial.
    right;right; split; trivial.
    apply isPEAddDerivation with entry; trivial.
Qed.

Lemma currentPartitionInPartitionsListAddDerivation  descChild s table idx entry :
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) ->
currentPartitionInPartitionsList s ->
currentPartitionInPartitionsList
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hentry Hpdflag Hcurpart.
unfold currentPartitionInPartitionsList in *.
cbn.
assert(Hpartitions : getPartitions multiplexer
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) 
                  (memory s) beqPage beqIndex |} = 
getPartitions multiplexer s).
apply getPartitionsAddDerivation with entry; trivial.
rewrite Hpartitions in *; clear Hpartitions; trivial.
Qed.

Lemma noDupMappedPagesListAddDerivation descChild s table idx entry :
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) ->
noDupMappedPagesList s ->
noDupMappedPagesList
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hentry Hpdflag.
unfold noDupMappedPagesList.
intros.
assert(Hpartitions : getPartitions multiplexer
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) 
                  (memory s) beqPage beqIndex |} = 
getPartitions multiplexer s).
apply getPartitionsAddDerivation with entry; trivial.
rewrite Hpartitions in *; clear Hpartitions; trivial.
assert (Hmapped : getMappedPages partition
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) 
                 (memory s) beqPage beqIndex |}=
         getMappedPages partition s).
apply getMappedPagesAddDerivation with entry;trivial.
rewrite Hmapped;clear Hmapped.
apply H;trivial.
Qed.

Lemma noDupConfigPagesListAddDerivation descChild s table idx entry :
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) ->
noDupConfigPagesList s ->
noDupConfigPagesList
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hentry Hpdflag.
unfold noDupConfigPagesList.
intros.
assert(Hpartitions : getPartitions multiplexer
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) 
                  (memory s) beqPage beqIndex |} = 
getPartitions multiplexer s).
apply getPartitionsAddDerivation with entry; trivial.
rewrite Hpartitions in *; clear Hpartitions; trivial.
assert ( getIndirections root  {|
        currentPartition := currentPartition s;
        memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |} 
        = getIndirections root s) as Hind. 
apply getIndirectionsAddDerivation with entry; trivial.
rewrite Hind.
apply H with idxroot partition; trivial.
rewrite <- nextEntryIsPPAddDerivation with entry in H2; trivial.
Qed.

Lemma parentInPartitionListAddDerivation descChild s table idx entry :
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) ->
parentInPartitionList s ->
parentInPartitionList
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hentry Hpdflag.
unfold parentInPartitionList.
intros.
assert(Hpartitions : getPartitions multiplexer
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) 
                  (memory s) beqPage beqIndex |} = 
getPartitions multiplexer s).
apply getPartitionsAddDerivation with entry; trivial.
rewrite Hpartitions in *; clear Hpartitions; trivial.
rewrite <- nextEntryIsPPAddDerivation with entry in H1; trivial.
apply H with partition; trivial.
Qed.

Lemma getPDFlagAddDerivation sh1 va descChild table idx entry s:
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) ->
getPDFlag sh1 va
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) 
  (memory s) beqPage beqIndex |} = getPDFlag sh1 va s.
Proof.
intros Hentry;
unfold getPDFlag.
case_eq( StateLib.getNbLevel);intros;trivial.
assert(Hind :getIndirection sh1 va l (nbLevel - 1)
          {|
          currentPartition := currentPartition s;
          memory := add table idx (VE {| pd := false; va := descChild |}) 
          (memory s) beqPage beqIndex |} = 
      getIndirection sh1 va l (nbLevel - 1) s).
apply getIndirectionAddDerivation with entry;trivial.
rewrite Hind;clear Hind.
case_eq( getIndirection sh1 va l (nbLevel - 1) s);intros;trivial.
case_eq(p =? defaultPage);intros;trivial.
cbn.

assert(StateLib.readPDflag p (StateLib.getIndexOfAddr va fstLevel)
    (add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex) = 
    StateLib.readPDflag p (StateLib.getIndexOfAddr va fstLevel) (memory s) ).
{ unfold StateLib.readPDflag in *.
cbn.
case_eq(beqPairs (table, idx) (p, StateLib.getIndexOfAddr va fstLevel) beqPage beqIndex);
intros Hpairs.
+ apply beqPairsTrue in Hpairs.
  destruct Hpairs.
  subst.
  rewrite Hentry in *.
  cbn.
  destruct H0;
  symmetry. assumption.
  now contradict H0.
+ apply beqPairsFalse in Hpairs.
  assert(Hmemory: lookup p (StateLib.getIndexOfAddr va fstLevel) (removeDup table idx (memory s) beqPage beqIndex)
    beqPage beqIndex = lookup p (StateLib.getIndexOfAddr va fstLevel) (memory s) beqPage beqIndex).
    apply removeDupIdentity;intuition.
   rewrite Hmemory.
   trivial. }
   rewrite H3;trivial.
Qed.

Lemma accessibleVAIsNotPartitionDescriptorAddDerivation descChild s table idx entry :
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) ->
accessibleVAIsNotPartitionDescriptor s -> 
accessibleVAIsNotPartitionDescriptor
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hentry Hpdflag.
unfold accessibleVAIsNotPartitionDescriptor.
intros.
assert(Hpd : StateLib.getPd partition
        (memory
           {|
           currentPartition := currentPartition s;
           memory := add table idx (VE {| pd := false; va := descChild |})
            (memory s) beqPage beqIndex |}) =
       StateLib.getPd partition (memory s)).
apply getPdAddDerivation with entry;trivial.
rewrite Hpd in *;clear Hpd.
assert(Hsh1 : StateLib.getFstShadow partition
        (memory
           {|
           currentPartition := currentPartition s;
           memory := add table idx (VE {| pd := false; va := descChild |})
            (memory s) beqPage beqIndex |}) =
       StateLib.getFstShadow partition (memory s)).
apply getFstShadowAddDerivation with entry;trivial.
rewrite Hsh1 in *;clear Hsh1.
assert(Haccess : getAccessibleMappedPage pd
                  {|
                  currentPartition := currentPartition s;
                  memory := add table idx (VE {| pd := false; va := descChild |}) 
                  (memory s) beqPage beqIndex |} va =
                getAccessibleMappedPage pd s va).
apply getAccessibleMappedPageAddDerivation with entry ;trivial.
rewrite Haccess in *;clear Haccess.
assert(Hpart : getPartitions multiplexer
                  {|
                  currentPartition := currentPartition s;
                  memory := add table idx (VE {| pd := false; va := descChild |}) 
                  (memory s) beqPage beqIndex |} = getPartitions multiplexer s).
apply getPartitionsAddDerivation with entry;trivial.
rewrite Hpart in *;clear Hpart.
assert(getPDFlag sh1 va
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |} 
  = getPDFlag sh1 va s).
apply getPDFlagAddDerivation with entry;trivial.
rewrite H4.
apply H with partition pd page;trivial.
Qed.

Lemma getVirtualAddressSh2AddDerivation sh2 s descChild table idx va entry:
  lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
getVirtualAddressSh2 sh2 s va =
getVirtualAddressSh2 sh2
    {|
    currentPartition := currentPartition s;
    memory := add table idx (VE {| pd := false; va := descChild |}) 
    (memory s) beqPage beqIndex |} va.
Proof.
intros.
unfold getVirtualAddressSh2.
case_eq(StateLib.getNbLevel);trivial.
intros nbL HnbL.
symmetry in HnbL. 
simpl.
rewrite  getIndirectionAddDerivation with sh2 table idx descChild s entry va  nbL (nbLevel -1);
trivial.
case_eq( getIndirection sh2 va nbL (nbLevel - 1) s);trivial.
intros lastIndirection Hind.
simpl.
case_eq(defaultPage =? lastIndirection);intros;trivial.
symmetry. 
apply readVirtualAddDerivation with entry;trivial.
Qed.

Lemma isAccessibleMappedPageInParentAddDerivattion partition (* nbL *) entry va
 accessiblePage table idx descChild s:
  lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
isAccessibleMappedPageInParent partition va accessiblePage s =
isAccessibleMappedPageInParent partition va accessiblePage
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |}.
Proof.
unfold isAccessibleMappedPageInParent.
simpl.
intros.
rewrite  getSndShadowAddDerivation with partition descChild table idx s entry ;trivial.
case_eq (getSndShadow partition (memory s));trivial.
intros sh2 Hsh2.
rewrite <- getVirtualAddressSh2AddDerivation with sh2 s descChild table idx va entry;trivial.
case_eq(getVirtualAddressSh2 sh2 s va);trivial.
intros vaInParent HvaInParent.
rewrite getParentAddDerivation with  partition descChild table idx s entry ;trivial.
case_eq(getParent partition (memory s));trivial.
intros parent Hparent.
rewrite getPdAddDerivation with  parent descChild table idx s entry;trivial.
case_eq(StateLib.getPd parent (memory s) );trivial.
intros pdParent HpdParent.
rewrite <- getAccessibleMappedPageAddDerivation  with 
pdParent descChild table idx entry vaInParent s;trivial.

Qed.

Lemma accessibleChildPhysicalPageIsAccessibleIntoParentAddDerivation
 (descChild : vaddr) table idx entry (s : state): 
( StateLib.readPDflag table idx (memory s) = Some false \/
StateLib.readPDflag table idx (memory s) = None)-> 
 lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
accessibleChildPhysicalPageIsAccessibleIntoParent s -> 
accessibleChildPhysicalPageIsAccessibleIntoParent
{|
currentPartition := currentPartition s;
memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hpdflag Hlookup Haccess .
set (s' :=  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) 
   (memory s) beqPage beqIndex |}) in *.   
unfold accessibleChildPhysicalPageIsAccessibleIntoParent.
intros  partition va pd  accessiblePage.
intros Hpart Hpd HaccessPage.
unfold s'.
assert(Hgetparts : getPartitions multiplexer s' = getPartitions multiplexer s).
{ apply getPartitionsAddDerivation with entry; trivial. }
rewrite Hgetparts in *.
clear Hgetparts.
simpl in *.
rewrite getPdAddDerivation with partition descChild table idx s  entry in Hpd ; trivial.
unfold s' in *.
rewrite getAccessibleMappedPageAddDerivation  
with pd descChild table idx entry va s in HaccessPage;trivial. 

rewrite <- isAccessibleMappedPageInParentAddDerivattion with partition entry
va accessiblePage table idx descChild s;trivial.
unfold accessibleChildPhysicalPageIsAccessibleIntoParent in *.
apply Haccess with pd;trivial.
Qed.

Lemma consistencyUpdtateSh1Structure (descChild : vaddr) table idx entry (s : state):
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) ->
consistency s -> 
consistency
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) 
              (memory s) beqPage beqIndex |}.
Proof.
intros.
unfold consistency in *.
split.
apply partitionDescriptorEntryAddDerivation with entry; intuition.
split.
apply dataStructurePdSh1Sh2asRootAddDerivation with entry; intuition.
split.
apply dataStructurePdSh1Sh2asRootAddDerivation with entry; intuition.
split.
apply dataStructurePdSh1Sh2asRootAddDerivation with entry; intuition.
split.
apply currentPartitionInPartitionsListAddDerivation with entry; intuition.
split.
apply noDupMappedPagesListAddDerivation with entry; intuition.
split.
apply noDupConfigPagesListAddDerivation with entry; intuition.
split.
apply parentInPartitionListAddDerivation with entry; intuition.
split.
apply accessibleVAIsNotPartitionDescriptorAddDerivation with entry; intuition.
apply accessibleChildPhysicalPageIsAccessibleIntoParentAddDerivation with entry;
intuition.
Qed.

Lemma getTableRootAddDerivation table1 idx1 table2 idx2 partition   
va idxVa (descChild : vaddr) entry (s : state) f :
lookup table2 idx2 (memory s) beqPage beqIndex = Some (VE entry) ->
StateLib.getIndexOfAddr va fstLevel = idxVa ->
(forall idx : index,
      StateLib.getIndexOfAddr va fstLevel = idx ->
      f table1 idx s /\ getTableAddrRoot table1 idx1 partition va s) -> 
getTableAddrRoot table1 idx1 partition va
  {|
  currentPartition := currentPartition s;
  memory := add table2 idx2 (VE {| pd := false; va := descChild |}) 
              (memory s) beqPage beqIndex |}.
Proof.
intros Hentry Hidxva (* Hpp *) Htableroot .
apply Htableroot in Hidxva.
destruct Hidxva as (Hpe & Hget).
clear Htableroot.
unfold getTableAddrRoot in *.
destruct Hget as (Hor & Hget).
split ;trivial; clear Hor.
intros tableroot Hpp.
rewrite <- nextEntryIsPPAddDerivation with entry in Hpp; trivial.
apply Hget in Hpp.
destruct Hpp as (nbL & Hnbl & stop & Hstop & Hgetind).
exists nbL;split; trivial.
exists stop; split;trivial.
rewrite <- Hgetind.
apply getIndirectionAddDerivation with entry; trivial.
Qed.

Lemma entryPresentFlagAddDerivation table1 idx1 table2 idx2   flag
 (descChild : vaddr) entry (s : state):
lookup table2 idx2 (memory s) beqPage beqIndex = Some (VE entry) -> 
entryPresentFlag table1 idx1 flag s ->
entryPresentFlag table1 idx1 flag
  {|
  currentPartition := currentPartition s;
  memory := add table2 idx2 (VE {| pd := false; va := descChild |}) 
              (memory s) beqPage beqIndex |}.
Proof.
intros Hentry Hep.
unfold entryPresentFlag in *.
cbn.
case_eq (beqPairs (table2, idx2) (table1, idx1) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry in *.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  table1 idx1 (removeDup table2 idx2(memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  table1 idx1  (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.

Lemma isEntryVAAddDerivation table1 idx1 table2 idx2 va 
 (descChild : vaddr) (s : state):
table1 <> table2 \/ idx1 <> idx2 -> 
isEntryVA table1 idx1 va s -> 
isEntryVA table1 idx1 va
    {|
    currentPartition := currentPartition s;
    memory := add table2 idx2 (VE {| pd := false; va := descChild |}) 
                (memory s) beqPage beqIndex |} .
Proof.
intros Hentry Hva.
unfold isEntryVA in *.
cbn.
assert(Hfalse : beqPairs (table2, idx2) (table1, idx1) beqPage beqIndex = false).
apply beqPairsFalse; intuition.

rewrite Hfalse.
assert (lookup  table1 idx1 (removeDup table2 idx2(memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  table1 idx1  (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.


Lemma isEntryPageAddDerivation table1 idx1 table2 idx2  addr
 (descChild : vaddr) entry (s : state):
lookup table2 idx2 (memory s) beqPage beqIndex = Some (VE entry) -> 
isEntryPage table1 idx1 addr s ->
isEntryPage table1 idx1 addr 
  {|
  currentPartition := currentPartition s;
  memory := add table2 idx2 (VE {| pd := false; va := descChild |}) 
              (memory s) beqPage beqIndex |}.
Proof.
intros Hentry Hep.
unfold isEntryPage in *.
cbn.
case_eq (beqPairs (table2, idx2) (table1, idx1) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry in *.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  table1 idx1 (removeDup table2 idx2(memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  table1 idx1  (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.

Lemma entryUserFlagAddDerivation table1 idx1 table2 idx2   flag
 (descChild : vaddr) entry (s : state):
lookup table2 idx2 (memory s) beqPage beqIndex = Some (VE entry) -> 
entryUserFlag table1 idx1 flag s ->
entryUserFlag table1 idx1 flag
  {|
  currentPartition := currentPartition s;
  memory := add table2 idx2 (VE {| pd := false; va := descChild |}) 
              (memory s) beqPage beqIndex |}.
Proof.
intros Hentry Heu.
unfold entryUserFlag in *.
cbn.
case_eq (beqPairs (table2, idx2) (table1, idx1) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry in *.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  table1 idx1 (removeDup table2 idx2(memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  table1 idx1  (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.

Lemma isPartitionFalseAddDerivation table idx descChild s :
isPartitionFalse table idx 
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) 
              (memory s) beqPage beqIndex |}.
Proof.
unfold isPartitionFalse.
cbn.
left.
unfold StateLib.readPDflag.
cbn.
assert(Htrue : beqPairs (table, idx) (table, idx) beqPage beqIndex = true).
apply beqPairsTrue;split;trivial.
rewrite Htrue.
cbn;trivial.
Qed.