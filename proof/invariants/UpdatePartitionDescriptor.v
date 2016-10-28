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
    This file contains several invariants of [updatePartitionDescriptor]  *)
Require Import Core.Internal Isolation Consistency WeakestPreconditions 
Invariants StateLib Model.Hardware Model.ADT Model.MAL 
DependentTypeLemmas Model.Lib InternalLemmas  PropagatedProperties UpdateMappedPageContent.
Require Import Coq.Logic.ProofIrrelevance Omega List Bool. 

Lemma updatePartitionDescriptorPropagatedProperties 

(idxroot : index) table1 idxVa1 pt1 va1  value1 value2 zero nullv presentConfigPagesList 
          presentPDChild presentRefChild presentSh1 presentSh2 pdChild currentPart 
          currentPD level ptRefChild descChild idxRefChild ptPDChild
          idxPDChild ptSh1Child shadow1 idxSh1  ptSh2Child shadow2 idxSh2 ptConfigPagesList
          idxConfigPagesList  currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild
          ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild
          phySh1Child phySh2Child phyConfigPagesList phyDescChild  idxPR idxPD idxSH1 idxSH2 idxSH3
        idxPPR  : 
presentRefChild = true  /\ presentPDChild = true  /\
presentConfigPagesList = true /\ presentSh1 = true /\ presentSh2 = true -> 
{{ fun s : state =>
  (propagatedProperties  false false false false
   pdChild currentPart currentPD level ptRefChild descChild idxRefChild true ptPDChild idxPDChild
      true ptSh1Child shadow1 idxSh1 true ptSh2Child shadow2 idxSh2 true ptConfigPagesList idxConfigPagesList true
      currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild ptSh1ChildFromSh1 derivedSh1Child
      childSh2 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child
      phyConfigPagesList phyDescChild s /\
    zero = CIndex 0 /\
    (forall idx : index, StateLib.readPhyEntry phySh2Child idx (memory s) = Some defaultPage) /\
    (forall idx : index, StateLib.readPhyEntry phySh1Child idx (memory s) = Some defaultPage) /\
    (forall idx : index, StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage) /\
    StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage /\
    (forall idx : index,
     idx <> CIndex (tableSize - 1) ->
     Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) /\
    (forall idx : index,
     Nat.Even idx -> exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) /\
    nullv = defaultVAddr /\ idxPR = PRidx /\ idxPD = PDidx /\ idxSH1 = sh1idx /\ idxSH2 = sh2idx /\ idxSH3 = sh3idx) /\
   idxPPR = PPRidx  /\
   (forall partition : page,
          In partition (getPartitions multiplexer s) ->
          partition = table1 \/ In table1 (getConfigPagesAux partition s) ->False) /\ 
   (defaultPage =? table1) = false /\
   isEntryPage pt1 idxVa1 table1 s /\
   StateLib.getIndexOfAddr va1 fstLevel = idxVa1 /\
   (forall idx : index,
        StateLib.getIndexOfAddr va1 fstLevel = idx ->
        isPE pt1 idx s /\ getTableAddrRoot pt1 PDidx (currentPartition s) va1 s) /\
  entryPresentFlag pt1 idxVa1 true s  /\
  false = checkVAddrsEqualityWOOffset nbLevel va1 pdChild level /\
  false = checkVAddrsEqualityWOOffset nbLevel va1 shadow1 level /\
  false = checkVAddrsEqualityWOOffset nbLevel va1 shadow2 level /\
  false = checkVAddrsEqualityWOOffset nbLevel va1 list level /\
  nextEntryIsPP (currentPartition s) PDidx currentPD s /\
  (defaultPage =? pt1) = false /\
  idxroot < tableSize - 1 }} 

Internal.updatePartitionDescriptor table1 idxroot value1 value2 
{{ fun _ s  =>
     (propagatedProperties  false false false false
     pdChild currentPart currentPD level ptRefChild descChild idxRefChild true ptPDChild idxPDChild
      true ptSh1Child shadow1 idxSh1 true ptSh2Child shadow2 idxSh2 true ptConfigPagesList idxConfigPagesList true
      currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild ptSh1ChildFromSh1 derivedSh1Child
      childSh2 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child
      phyConfigPagesList phyDescChild s /\
    zero = CIndex 0 /\
    (forall idx : index, StateLib.readPhyEntry phySh2Child idx (memory s) = Some defaultPage) /\
    (forall idx : index, StateLib.readPhyEntry phySh1Child idx (memory s) = Some defaultPage) /\
    (forall idx : index, StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage) /\
    StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage /\
    (forall idx : index,
     idx <> CIndex (tableSize - 1) ->
     Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) /\
    (forall idx : index,
     Nat.Even idx -> exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) /\
    nullv = defaultVAddr /\ idxPR = PRidx /\ idxPD = PDidx /\ idxSH1 = sh1idx /\ idxSH2 = sh2idx /\ idxSH3 = sh3idx) /\
   idxPPR = PPRidx   }}.
Proof.
intros Hlegit.
unfold updatePartitionDescriptor.
eapply bindRev.
(** writeVirtual **)
   eapply weaken.
   eapply WP.writeVirtual.
   simpl;intros.
   try repeat rewrite and_assoc in H.
    subst.
   pattern s in H.
    match type of H with 
    | ?HT s => instantiate (1 := fun tt s => HT s )
    end.
   simpl in *.
   split.
   intuition.
    apply propagatedPropertiesUpdateMappedPageData; trivial.
    split.
    intuition.
(*     split.
    unfold propagatedProperties in *.
  unfold consistency in *.
  assert(Hin : currentPartitionInPartitionsList s)by
  intuition.

  apply mappedPageIsNotPTable with currentPart currentPD isPE PDidx 
  pdChild idxPDChild s ;
  intuition.
  subst.
  unfold currentPartitionInPartitionsList.
  trivial.
  subst.
  unfold currentPartitionInPartitionsList.
  trivial.
  intuition. *)
  assert(getPartitions multiplexer {|
      currentPartition := currentPartition s;
      memory := add table1 idxroot (VA value2) (memory s) beqPage beqIndex |} = 
      getPartitions multiplexer s) as Hpartions.
    {
      apply getPartitionsUpdateMappedPageData ; trivial.
      + unfold getPartitions.
        destruct nbPage;simpl;left;trivial.
      + intuition.
      + assert(Hfalse : (defaultPage =? table1) = false) by intuition.
        apply beq_nat_false in Hfalse.
        unfold not; intros.
        apply Hfalse.
        subst;trivial.
      + unfold propagatedProperties in *.
        unfold consistency in *.
        intuition.  }
    rewrite Hpartions in *; trivial.
    assert(Hconfig: forall partition : page,
     In partition (getPartitions multiplexer s) ->
     partition = table1 \/ In table1 (getConfigPagesAux partition s) -> False)
     by intuition.
    assert(Hcurpart : In (currentPartition s) (getPartitions multiplexer s)).
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *.
    intuition.
    assert(Hpde : partitionDescriptorEntry s).
    unfold propagatedProperties in *.
    unfold consistency in *.
    intuition.
    assert(Htableroot1 : forall idx : index,
          StateLib.getIndexOfAddr va1 fstLevel = idx ->
          isPE pt1 idx s /\ getTableAddrRoot pt1 PDidx (currentPartition s) va1 s) by intuition.
    intuition.
    assert (Htable : forall idx : index, StateLib.readPhyEntry phySh2Child idx (memory s) = Some defaultPage)
    by intuition.
    { generalize (Htable idx); clear Htable; intros Htable.
    rewrite <- Htable.
    symmetry.
    apply readPhyEntryUpdateMappedPageData; trivial.
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
    subst.

         apply readMappedPageDataUpdateMappedPageData 
    with  (currentPartition s)  ptSh2Child pt1 
    (StateLib.getIndexOfAddr shadow2 fstLevel)  
    (StateLib.getIndexOfAddr va1 fstLevel)
       shadow2 va1 level s; trivial.
    rewrite checkVAddrsEqualityWOOffsetPermut.
    assumption. } 
    assert (Htable : forall idx : index, StateLib.readPhyEntry phySh1Child idx (memory s) = Some defaultPage)
    by intuition.
    { generalize (Htable idx); clear Htable; intros Htable.
      rewrite <- Htable.
      symmetry.
     apply readPhyEntryUpdateMappedPageData; trivial.
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
    subst.
      apply readMappedPageDataUpdateMappedPageData 
      with  (currentPartition s)  ptSh1Child pt1 
      (StateLib.getIndexOfAddr shadow1 fstLevel)  
      (StateLib.getIndexOfAddr va1 fstLevel)
         shadow1 va1 level s; trivial.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      subst.
      intuition.
      rewrite checkVAddrsEqualityWOOffsetPermut.
      assumption. }
    assert (Htable : forall idx : index, StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage)
    by intuition.
    { generalize (Htable idx); clear Htable; intros Htable.
      rewrite <- Htable.
      symmetry.
      apply readPhyEntryUpdateMappedPageData; trivial.
      unfold propagatedProperties in *.
      unfold consistency in *.
      unfold not.
      intros Hfalse.
      intuition.
      symmetry in Hfalse.
      contradict Hfalse.
      subst.
      apply readMappedPageDataUpdateMappedPageData 
      with  (currentPartition s)  ptPDChild pt1 
      (StateLib.getIndexOfAddr pdChild fstLevel)  
      (StateLib.getIndexOfAddr va1 fstLevel)
         pdChild va1 level s; trivial.
      intuition.
      rewrite checkVAddrsEqualityWOOffsetPermut.
      assumption. }
      
   assert (Htable : StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage)
    by intuition.
    { rewrite <- Htable.
      apply readPhysicalUpdateMappedPageData; trivial.
      unfold propagatedProperties in *.
      unfold consistency in *.
      unfold not.
      intros Hfalse.
      intuition.
      symmetry in Hfalse.
      contradict Hfalse.
      subst.
      apply readMappedPageDataUpdateMappedPageData 
      with  (currentPartition s)  ptConfigPagesList pt1 
      (StateLib.getIndexOfAddr list fstLevel)  
      (StateLib.getIndexOfAddr va1 fstLevel)
         list va1 level s; trivial.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      subst.
      intuition.
      rewrite checkVAddrsEqualityWOOffsetPermut.
      assumption. }
       assert (Htable : StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr)
    by intuition.
    { rewrite <- Htable.
      apply readVirtualUpdateMappedPageData; trivial.
      unfold propagatedProperties in *.
      unfold consistency in *.
      unfold not.
      intros Hfalse.
      intuition.
      symmetry in Hfalse.
      contradict Hfalse.
      subst.
      apply readMappedPageDataUpdateMappedPageData 
      with  (currentPartition s)  ptConfigPagesList pt1 
      (StateLib.getIndexOfAddr list fstLevel)  
      (StateLib.getIndexOfAddr va1 fstLevel)
         list va1 level s; trivial.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      subst.
      intuition.
      rewrite checkVAddrsEqualityWOOffsetPermut.
      assumption. }
     assert (Htable : exists idxValue : index, 
     StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue)
    by intuition.
    destruct Htable as (idxValue & Htable).
    exists idxValue.
    { rewrite <- Htable.
      apply readIndexUpdateMappedPageData; trivial.
      unfold propagatedProperties in *.
      unfold consistency in *.
      unfold not.
      intros Hfalse.
      intuition.
      symmetry in Hfalse.
      contradict Hfalse.
      subst.
      apply readMappedPageDataUpdateMappedPageData 
      with  (currentPartition s)  ptConfigPagesList pt1 
      (StateLib.getIndexOfAddr list fstLevel)  
      (StateLib.getIndexOfAddr va1 fstLevel)
         list va1 level s; trivial.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      subst.
      intuition.
      rewrite checkVAddrsEqualityWOOffsetPermut.
      assumption. }
    assert(Hpart : In partition (getPartitions multiplexer s)) by trivial.
    apply Hconfig in Hpart.
    now contradict Hpart.
    left; trivial.
    assert(Hpart : In partition (getPartitions multiplexer s)) by trivial.
    apply Hconfig in Hpart.
    now contradict Hpart.
    right.
    assert(Hconfaux :getConfigPagesAux partition {|
                      currentPartition := currentPartition s;
                      memory := add table1 idxroot (VA value2) (memory s) beqPage beqIndex |} = 
                      getConfigPagesAux  partition s).
    { apply getConfigPagesAuxUpdateMappedPageData; trivial.
      unfold getConfigPages; unfold not; simpl.
      apply Hconfig; trivial. } 
    rewrite Hconfaux in *.
    assumption.
    apply isEntryPageUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with (currentPartition s)  currentPD isPE PDidx va1 idxVa1 s ;
    trivial. left;trivial.
    apply isPEUpdateUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with (currentPartition s)  currentPD isPE PDidx va1 idxVa1 s ;
    trivial. left;trivial.
    apply Htableroot1; trivial.
    apply getTableAddrRootUpdateMappedPageData; trivial.
    assert (isPE pt1 idx s /\ getTableAddrRoot pt1 PDidx (currentPartition s)  va1 s)
    as ( _ & Hget1).
    apply Htableroot1; trivial.
    trivial.
    apply entryPresentFlagUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with (currentPartition s)   currentPD isPE PDidx va1 idxVa1 s ;
    trivial. left;trivial.
    apply nextEntryIsPPUpdateMappedPageData; trivial.
    intros [].
 (** MALInternal.Index.succ **) 
   eapply bindRev.
   eapply WP.weaken. 
   eapply Invariants.Index.succ.
   intros.
   simpl.
   split.
   try repeat rewrite and_assoc in H.  
   pattern s in H.
   eassumption.
   repeat rewrite and_assoc in H.
   intuition.
   intros PRidxsucc.
(** writePhysical**)
  eapply weaken.
  eapply WP.writePhysical.
  simpl;intros.
  try repeat rewrite and_assoc in H.
  subst.
  pattern s in H.
  simpl in *.
  intuition.
  subst.
   apply propagatedPropertiesUpdateMappedPageData; trivial.
     assert (Htable : forall idx : index, StateLib.readPhyEntry phySh2Child idx (memory s) = Some defaultPage)
    by intuition.
    { generalize (Htable idx); clear Htable; intros Htable.
      rewrite <- Htable.
      symmetry.
      apply readPhyEntryUpdateMappedPageData; trivial.
      unfold propagatedProperties in *.
      unfold consistency in *.
      unfold not.
      intros Hfalse.
      intuition.
      symmetry in Hfalse.
      contradict Hfalse.
      subst.
      apply readMappedPageDataUpdateMappedPageData 
      with  (currentPartition s)  ptSh2Child pt1 
      (StateLib.getIndexOfAddr shadow2 fstLevel)  
      (StateLib.getIndexOfAddr va1 fstLevel)
         shadow2 va1 level s; trivial.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      subst.
      intuition.
      rewrite checkVAddrsEqualityWOOffsetPermut.
      assumption. } 
    assert (Htable : forall idx : index, StateLib.readPhyEntry phySh1Child idx (memory s) = Some defaultPage)
    by intuition.
    { generalize (Htable idx); clear Htable; intros Htable.
      rewrite <- Htable.
      symmetry.
      apply readPhyEntryUpdateMappedPageData; trivial.
      unfold propagatedProperties in *.
      unfold consistency in *.
      unfold not.
      intros Hfalse.
      intuition.
      symmetry in Hfalse.
      contradict Hfalse.
      subst.
      apply readMappedPageDataUpdateMappedPageData 
      with  (currentPartition s)  ptSh1Child pt1 
      (StateLib.getIndexOfAddr shadow1 fstLevel)  
      (StateLib.getIndexOfAddr va1 fstLevel)
         shadow1 va1 level s; trivial.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      subst.
      intuition.
      rewrite checkVAddrsEqualityWOOffsetPermut.
      assumption. }
    assert (Htable : forall idx : index, StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage)
    by intuition.
    { generalize (Htable idx); clear Htable; intros Htable.
      rewrite <- Htable.
      symmetry.
      apply readPhyEntryUpdateMappedPageData; trivial.
      unfold propagatedProperties in *.
      unfold consistency in *.
      unfold not.
      intros Hfalse.
      intuition.
      symmetry in Hfalse.
      contradict Hfalse.
      subst.
      apply readMappedPageDataUpdateMappedPageData 
      with  (currentPartition s)  ptPDChild pt1 
      (StateLib.getIndexOfAddr pdChild fstLevel)  
      (StateLib.getIndexOfAddr va1 fstLevel)
         pdChild va1 level s; trivial.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      subst.
      intuition.
      rewrite checkVAddrsEqualityWOOffsetPermut.
      assumption. }  
   assert (Htable : StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage)
    by intuition.
    { rewrite <- Htable.
      apply readPhysicalUpdateMappedPageData; trivial.
      unfold propagatedProperties in *.
      unfold consistency in *.
      unfold not.
      intros Hfalse.
      intuition.
      symmetry in Hfalse.
      contradict Hfalse.
      subst.
      apply readMappedPageDataUpdateMappedPageData 
      with  (currentPartition s)  ptConfigPagesList pt1 
      (StateLib.getIndexOfAddr list fstLevel)  
      (StateLib.getIndexOfAddr va1 fstLevel)
         list va1 level s; trivial.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      subst.
      intuition.
      rewrite checkVAddrsEqualityWOOffsetPermut.
      assumption. }
       assert (Htable : StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr)
    by intuition.
    { rewrite <- Htable.
      apply readVirtualUpdateMappedPageData; trivial.
      unfold propagatedProperties in *.
      unfold consistency in *.
      unfold not.
      intros Hfalse.
      intuition.
      symmetry in Hfalse.
      contradict Hfalse.
      subst.
      apply readMappedPageDataUpdateMappedPageData 
      with  (currentPartition s)  ptConfigPagesList pt1 
      (StateLib.getIndexOfAddr list fstLevel)  
      (StateLib.getIndexOfAddr va1 fstLevel)
         list va1 level s; trivial.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      subst.
      intuition.
      rewrite checkVAddrsEqualityWOOffsetPermut.
      assumption. }
     assert (Htable : exists idxValue : index, 
     StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue)
    by intuition.
    destruct Htable as (idxValue & Htable).
    exists idxValue.
    { rewrite <- Htable.
      apply readIndexUpdateMappedPageData; trivial.
      unfold propagatedProperties in *.
      unfold consistency in *.
      unfold not.
      intros Hfalse.
      intuition.
      symmetry in Hfalse.
      contradict Hfalse.
      subst.
      apply readMappedPageDataUpdateMappedPageData 
      with  (currentPartition s)  ptConfigPagesList pt1 
      (StateLib.getIndexOfAddr list fstLevel)  
      (StateLib.getIndexOfAddr va1 fstLevel)
         list va1 level s; trivial.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      subst.
      intuition.
      rewrite checkVAddrsEqualityWOOffsetPermut.
      assumption. }
Qed. 


Lemma updatePartitionDescriptorNewProperty (phyDescChild : page) (value2 : vaddr) value1 (idxPR : index) :
 {{ fun s : state =>  idxPR < tableSize - 1}} 
     Internal.updatePartitionDescriptor phyDescChild idxPR value1 value2
{{ fun _ s => isVA phyDescChild idxPR  s /\ nextEntryIsPP phyDescChild idxPR value1 s}}.
Proof.
unfold updatePartitionDescriptor.
eapply bindRev.
(** writeVirtual **) 
eapply weaken.
eapply WP.writeVirtual.
simpl.
intros.
pattern s in H.
match type of H with 
| ?HT s => instantiate (1 := fun tt s => HT s /\ 
         StateLib.readVirtual phyDescChild idxPR s.(memory) = Some value2 )
end.
simpl in *.
split; trivial.
unfold StateLib.readVirtual.
cbn.
assert (Htrue :Lib.beqPairs (phyDescChild, idxPR) (phyDescChild, idxPR) beqPage beqIndex
= true).
apply beqPairsTrue;split;trivial.
rewrite Htrue; trivial.
intros [].
(** MALInternal.Index.succ **) 
eapply bindRev.
eapply WP.weaken. 
eapply Invariants.Index.succ.
intros.
simpl.
split.
try repeat rewrite and_assoc in H.  
pattern s in H.
eassumption.
intuition.
intros idxsucc.
(** writeVirtual **) 
eapply weaken.
eapply WP.writePhysical.
simpl.
intros.
split.
(** isVA postcondition **)
unfold isVA.
cbn.
assert(Hidxsucc : idxsucc <> idxPR).
destruct H.
unfold not; intros.
symmetry in H1.
contradict H1.
apply indexSuccEqFalse; trivial.
assert(Hfalse : beqPairs (phyDescChild, idxsucc) (phyDescChild, idxPR) beqPage beqIndex
                = false).
apply beqPairsFalse.
right; trivial.
rewrite Hfalse.
destruct H as ((Hixd & Hreadv )& Hsucc).
unfold StateLib.readVirtual in *.
assert(Hmemory : lookup phyDescChild idxPR (removeDup phyDescChild idxsucc (memory s) beqPage beqIndex) beqPage
        beqIndex = lookup phyDescChild idxPR (memory s) beqPage beqIndex).
{ apply removeDupIdentity; trivial.
  right.
  unfold not; intros.
  subst.
  now contradict Hidxsucc.  }
rewrite Hmemory.
destruct (lookup phyDescChild idxPR (memory s) beqPage beqIndex ); 
try now contradict Hreadv.
destruct v; try now contradict Hreadv.
trivial.
(** nextEntryIsPP postcondition **)
unfold nextEntryIsPP.
destruct H.
rewrite H0.
cbn.
assert (Htrue :Lib.beqPairs(phyDescChild, idxsucc) (phyDescChild, idxsucc) beqPage beqIndex
              = true).
apply beqPairsTrue;split;trivial.
rewrite Htrue; trivial.
Qed.

Lemma updatePartitionDescriptorPropagatedProperties2 table (idx1 idx2: index) pageValue1 va  pageValue2 : 
{{ fun s : state => idx2 < tableSize - 1 /\ idx1 < tableSize - 1/\ idx1 <> idx2 /\  
(exists succidx1, StateLib.Index.succ idx1 = Some succidx1  /\ succidx1 <> idx2) /\
(exists succidx2, StateLib.Index.succ idx2 = Some succidx2 /\ succidx2 <> idx1) /\
isVA table idx1 s /\ nextEntryIsPP table idx1 pageValue1 s}}
 Internal.updatePartitionDescriptor table idx2 pageValue2 va 
{{ fun (_ : unit) (s : state) =>isVA table idx1 s /\  nextEntryIsPP table idx1 pageValue1 s }}.
Proof.
unfold updatePartitionDescriptor.
eapply bindRev.
(** writeVirtual **)
eapply weaken.
eapply WP.writeVirtual.
simpl.
intros.
pattern s in H.
match type of H with 
| ?HT s => instantiate (1 := fun tt s => HT s )
end.
simpl in *.
intuition.
(** propagate isVA **)
unfold isVA in *.
cbn.
assert(Hfalse:  beqPairs (table, idx2) (table, idx1) beqPage beqIndex = false).
apply beqPairsFalse.
right.
unfold not; intros; subst.
now contradict H1.
rewrite Hfalse.
assert (Hmemory :  lookup table idx1 (removeDup table idx2 (memory s) beqPage beqIndex)
    beqPage beqIndex = lookup table idx1 (memory s) beqPage beqIndex).
{ apply removeDupIdentity; right; unfold not; intros; subst; now contradict H1. }
rewrite Hmemory; assumption.
(** propagate nextEntryIsPP **)
destruct H2 as (idx1succ & Hidx1succ & Hnoteq).
unfold nextEntryIsPP in *.
rewrite Hidx1succ in *.
cbn.
assert(Hfalse:  beqPairs (table, idx2) (table, idx1succ) beqPage beqIndex = false).
apply beqPairsFalse.
right.
unfold not; intros; subst.
now contradict Hnoteq.
rewrite Hfalse.
assert (Hmemory :  lookup table idx1succ (removeDup table idx2 (memory s) beqPage beqIndex)
    beqPage beqIndex = lookup table idx1succ (memory s) beqPage beqIndex).
{ apply removeDupIdentity; right; unfold not; intros; subst; now contradict Hnoteq. }
rewrite Hmemory; assumption.
intros [].
(** MALInternal.Index.succ **) 
eapply bindRev.
eapply WP.weaken. 
eapply Invariants.Index.succ.
intros.
simpl.
split.
try repeat rewrite and_assoc in H.  
pattern s in H.
eassumption.
intuition.
simpl.
intros idxsucc.
(** writeVirtual **) 
eapply weaken.
eapply WP.writePhysical.
simpl.
intros.
destruct H as ((H & H1 & H2 & H3 & H4 & H5 & H7) & H6).
destruct H4 as (succidx2 & Hsuccidx2 & Hnoteq).
rewrite H6 in Hsuccidx2.
inversion Hsuccidx2; clear Hsuccidx2.
subst.
split.
(** propagate isVA **)
unfold isVA in *.
cbn.
assert(Hfalse:  beqPairs (table, succidx2) (table, idx1) beqPage beqIndex = false).
{ apply beqPairsFalse.
  right.
  unfold not; intros.
  intuition. }
rewrite Hfalse.
assert (Hmemory :  lookup table idx1 (removeDup table succidx2 (memory s) beqPage beqIndex)
beqPage beqIndex = lookup table idx1 (memory s) beqPage beqIndex).
{ apply removeDupIdentity; right;  unfold not; intros; subst; now contradict Hnoteq. }
rewrite Hmemory; assumption.
(** propagate nextEntryIsPP **)
unfold nextEntryIsPP in *.
destruct H3 as (succidx1 & Hsuccidx1 & Hnoteqsucc12).
rewrite Hsuccidx1 in *.
cbn.
assert(Hfalse:  beqPairs (table, succidx2) (table, succidx1) beqPage beqIndex = false).
apply beqPairsFalse.
right.
unfold not; intros; subst.
rewrite <- Hsuccidx1 in H6.
apply indexNotEqSuccNotEq in H2; trivial.
now contradict H2. 
rewrite Hfalse.
assert (Hmemory :  lookup table succidx1 (removeDup table succidx2 (memory s) beqPage beqIndex)
    beqPage beqIndex = lookup table succidx1 (memory s) beqPage beqIndex).
{ apply removeDupIdentity; right.
  unfold not; intros. subst.
  rewrite <- Hsuccidx1 in H6.
  apply indexNotEqSuccNotEq in H2; trivial.
  now contradict H2.  }
rewrite Hmemory; assumption.
Qed.

