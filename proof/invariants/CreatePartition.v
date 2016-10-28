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
    This file contains the invariant of [createPartition]. 
    We prove that this PIP service preserves the isolation property *)
Require Import Model.ADT Model.Hardware Core.Services Isolation
Consistency Invariants WeakestPreconditions Model.Lib StateLib
Model.MAL InitConfigPagesList InitPEntryTable DependentTypeLemmas  GetTableAddr 
WriteAccessible WriteAccessibleRec UpdateMappedPageContent InternalLemmas  Lib
UpdatePartitionDescriptor PropagatedProperties UpdateShadow1Structure.
 Require Import Omega Bool  Coq.Logic.ProofIrrelevance List.

Lemma createPartition (descChild pdChild shadow1 shadow2 list : vaddr) :
{{fun s => partitionsIsolation s  /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }} 
createPartition descChild pdChild shadow1 shadow2 list  
{{fun _ s  => partitionsIsolation s  /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}.
Proof.
unfold createPartition.
eapply WP.bindRev.
eapply WP.weaken. 
(** getNbLevel **)
eapply Invariants.getNbLevel.
simpl. intros.
pattern s in H.
eapply H.
intros level.
(** Vaddrs Eq **)
eapply WP.bindRev.
eapply WP.weaken.
eapply Invariants.checkVAddrsEqualityWOOffset.
simpl.
intros.
pattern s in H.
eapply H.
intros. 
repeat (eapply WP.bindRev; [ eapply WP.weaken ; 
              [ apply Invariants.checkVAddrsEqualityWOOffset | intros ; simpl; pattern s in H; eapply H ] 
                                | simpl; intros  ]).
case_eq (a || a0 || a1 || a2 || a3 || a4 || a5 || a6 || a7 || a8); intros Hvaddrs.
eapply WP.weaken.
eapply WP.ret.
intros.
simpl. intuition.
try repeat rewrite orb_false_iff in Hvaddrs.
try repeat rewrite and_assoc in Hvaddrs.
intuition.
subst.
(** Kernel map **)
eapply WP.bindRev.
eapply WP.weaken.   
eapply Invariants.checkKernelMap.
intros. simpl.
pattern s in H. eapply H. 
intro.
repeat (eapply WP.bindRev; [ eapply WP.weaken ; 
              [ apply Invariants.checkKernelMap | intros; simpl; pattern s in H; eapply H ]
                                | simpl; intro ]).
                                simpl.
case_eq (negb a && negb a0 && negb a1 && negb a2 && negb a3).
intro Hkmap.
repeat rewrite andb_true_iff in Hkmap.
try repeat rewrite and_assoc in Hkmap.
repeat rewrite negb_true_iff in Hkmap. 
intuition.
subst.
eapply WP.bindRev. 
(** getCurPartition **)
      { eapply WP.weaken. 
        eapply Invariants.getCurPartition .
        cbn. 
        intros. 
        pattern s in H. 
        eapply H. }
      intro currentPart.   simpl.   
(** getPd **)  
      eapply WP.bindRev. 
        { eapply WP.weaken. 
          eapply Invariants.getPd.
          simpl.
          intros.
          split.
          (* try repeat rewrite and_assoc in H. *)
          pattern s in H. eapply H.
          unfold consistency in *.
          unfold partitionDescriptorEntry in *.
          unfold currentPartitionInPartitionsList in *.
          intuition          subst. trivial. 
          }
      intro currentPD. simpl. 
(* (** getNbLevel **)      
      eapply WP.bindRev.
      { eapply WP.weaken.
        eapply Invariants.getNbLevel.
        simpl.
        intros.
        try repeat rewrite and_assoc in H.
        pattern s in H.
        eapply H.
        }  intro level.  *)  
(** getTableAddr **)
      eapply WP.bindRev.
      eapply WP.weaken. 
      apply getTableAddr.
      simpl.
      intros s H.
      try repeat rewrite and_assoc in H.
      split.
      pattern s in H. 
      eapply H. subst.
      split. 
      intuition.
      split. unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition . 
      instantiate (1:= currentPart). subst. assumption.
      instantiate (1:= PDidx).
      split. intuition.
      destruct H as ( _ & _ & _ & Hcons & Hlevel  & _ & _ & _ &_ & _& _ & _ & _ & _ &_ & _ & _ & _ &_ & _& Hcp & Hrootpd ).
      exists currentPD.
      split. assumption.
      split.
      unfold consistency in *.
      destruct Hcons as (Hpd & _ & _ &_  & Hpr  & _). 
      unfold partitionDescriptorEntry in Hpd.
      unfold currentPartitionInPartitionsList in *.
      subst.
      generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.     
      assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx\/ PDidx = sh3idx \/ PDidx = PPRidx  \/ PDidx = PRidx ) as Htmp 
      by auto.
      generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry).
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx);
       [destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootpd | now contradict Hrootpd | 
       subst ; assumption| now contradict Hrootpd| now contradict Hrootpd ]  |now contradict Hrootpd] | now contradict Hrootpd].
      subst. 
      left. 
      split;trivial.
      intro ptRefChild. simpl.
 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      Focus 2.
      intros.
      destruct H as (H0 & H1).
      assert( (getTableAddrRoot' ptRefChild PDidx currentPart descChild s /\   ptRefChild = defaultPage) \/
     (forall idx : index,
      StateLib.getIndexOfAddr descChild fstLevel = idx ->
      isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s)).
      { 
      destruct H1 as [H1 |H1].
      + left. trivial. 
      + right. intros idx Hidx.
        destruct H1 as (Hget  & Hnew & H1).
        split. 
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(_& Hfalse) | [(_&Hfalse) |(Hpe &Htrue)]].
        - contradict Hfalse.
           unfold PDidx. unfold sh1idx.
           apply indexEqFalse ;
           assert (tableSize > tableSizeLowerBound).
           apply tableSizeBigEnough.
           unfold tableSizeLowerBound in *.
           omega.  apply tableSizeBigEnough.
           unfold tableSizeLowerBound in *.
           omega. apply tableSizeBigEnough. omega.
       - contradict Hfalse.
          unfold PDidx. unfold sh2idx.
         apply indexEqFalse;
         assert (tableSize > tableSizeLowerBound).
         apply tableSizeBigEnough.
         unfold tableSizeLowerBound in *.
         omega.  apply tableSizeBigEnough.
         unfold tableSizeLowerBound in *.
         omega. apply tableSizeBigEnough. omega.
      -
       assumption.
     - assumption.  } 
    assert (HP := conj H0 H).
    pattern s in HP.
    eapply HP.
(** comparePageToNull **) 
      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro ptRefChildIsnull. simpl.
      case_eq ptRefChildIsnull.
      { intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition. }
      intros HptRefChildNotNull. clear HptRefChildNotNull.
(** StateLib.getIndexOfAddr **)                
      eapply WP.bindRev.
      eapply WP.weaken.
      eapply Invariants.getIndexOfAddr.
      { simpl. intros.
        destruct H as ((H & [(Hptchild& Hnull) | Hptchild]) & Hptchildnotnull).
        + subst. contradict Hptchildnotnull. intro Hnull.
          apply beq_nat_false in Hnull. intuition.
        + subst.
          assert (HP := conj (conj H Hptchild) Hptchildnotnull).
          try repeat rewrite and_assoc in HP.
          pattern s in HP.
          eapply HP.  }
       intro idxRefChild. simpl.
(**readPresent **)
       eapply WP.bindRev.
       { eapply WP.weaken.
         eapply Invariants.readPresent. simpl.
         intros.
         split.
(*          try repeat rewrite and_assoc in H. *)
         pattern s in H.
         eapply H. 
         subst.
         destruct H as (H & Hidx).
         assert (forall idx : index,
         StateLib.getIndexOfAddr descChild fstLevel = idx -> isPE ptRefChild idx s/\ getTableAddrRoot ptRefChild PDidx currentPart descChild s).  
         intuition.
         apply H0 in Hidx. destruct Hidx. assumption.
       }
       intro presentRefChild. simpl.
(**readAccessible **)
       eapply WP.bindRev.
       { eapply WP.weaken.
         eapply Invariants.readAccessible. simpl.
         intros.
         split.
(*          try repeat rewrite and_assoc in H. *)
         pattern s in H.
         eapply H. 
         subst.
         apply entryPresentFlagIsPE with presentRefChild;intuition. 
        }
       intros accessibleChild. simpl.
(** getTableAddr **)
      eapply WP.bindRev.
      eapply WP.weaken. 
      apply getTableAddr.
      simpl.
      intros s H.
      try repeat rewrite and_assoc in H.
      split.
      pattern s in H. 
      eapply H. subst.
      split. 
      intuition.
      split. 
      instantiate (1:= currentPart). intuition. subst. unfold consistency in *. 
      unfold  currentPartitionInPartitionsList in *. intuition.
      instantiate (1:= PDidx).
      split. intuition.
       destruct H as ( _ & _ & _& Hcons  & Hlevel  & _ & _ & _ &_ & _& _ & _ & _ & _ &_ & _ & _ & _ &_ & _& Hcp & Hrootpd & H).
      exists currentPD.
      split. assumption.
      split.
      unfold consistency in *.
      destruct Hcons as (Hpd & _ & _ &_  & Hpr  & _). 
      unfold partitionDescriptorEntry in Hpd.
      unfold currentPartitionInPartitionsList in *.
      subst.
      generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.     
      assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/PDidx = sh3idx \/ PDidx = PPRidx  \/ PDidx = PRidx ) as Htmp 
      by auto.
      generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry).
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx);
       [destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootpd | now contradict Hrootpd | 
       subst ; assumption| now contradict Hrootpd| now contradict Hrootpd ]  |now contradict Hrootpd] | now contradict Hrootpd].

      subst. left. split;trivial.
           intro ptPDChild. simpl. 
 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      Focus 2.
      intros.
      destruct H as (H0 & H1).
      assert( (getTableAddrRoot'  ptPDChild PDidx currentPart pdChild s /\    ptPDChild = defaultPage) \/
     (forall idx : index,
      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
      isPE  ptPDChild idx s /\ getTableAddrRoot ptPDChild  PDidx currentPart pdChild s)).
      { 
      destruct H1 as [H1 |H1].
      + left. trivial. 
      + right. intros idx Hidx.
      
        destruct H1 as (Hget  & Hnew & H1).

        split. 
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(_& Hfalse) | [(_&Hfalse) |(Hpe &Htrue)]].
        - contradict Hfalse.
         
       unfold PDidx. unfold sh1idx.
       apply indexEqFalse ;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega.
       - contradict Hfalse.
          unfold PDidx. unfold sh2idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega.
      -
       assumption.
     - assumption.  } 
    assert (HP := conj H0 H).

        pattern s in HP.
        eapply HP.      
(** comparePageToNull **) 
      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro ptPDChildIsnull. simpl.
      case_eq ptPDChildIsnull.
      { intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition. }
      intros HptRefChildNotNull. clear HptRefChildNotNull.
(** StateLib.getIndexOfAddr         *)        
      eapply WP.bindRev.
      eapply WP.weaken.
      eapply Invariants.getIndexOfAddr.
      { simpl. intros. 
        destruct H as ((H & [(Hptchild & Hnull) | Hptchild]) & Hptchildnotnull).
        + subst. contradict Hptchildnotnull. intro Hnull.  apply beq_nat_false in Hnull. intuition.
        + subst.
          assert (HP := conj (conj H Hptchild) Hptchildnotnull).
(*           try repeat rewrite and_assoc in HP. *)
          pattern s in HP.
          eapply HP.  }
       intro idxPDChild. simpl.
(**readPresent **)
       eapply WP.bindRev.
       { eapply WP.weaken.
         eapply Invariants.readPresent. simpl.
         intros.
         split.
(*          try repeat rewrite and_assoc in H. *)
         pattern s in H.
         eapply H. 
         subst.
         destruct H as (H & Hidx).
         assert (forall idx : index,
         StateLib.getIndexOfAddr pdChild fstLevel = idx -> isPE ptPDChild idx s
         /\ getTableAddrRoot ptPDChild PDidx currentPart pdChild s).  
         { intuition. }
         
         apply H0 in Hidx. destruct Hidx; assumption.
       }
       intro presentPDChild. simpl.
(**readAccessible **)
       eapply WP.bindRev.
       { eapply WP.weaken.
         eapply Invariants.readAccessible. simpl.
         intros.
         split.
(*          try repeat rewrite and_assoc in H. *)
         pattern s in H.
         eapply H. 
         subst.
         apply entryPresentFlagIsPE with presentPDChild;intuition. }
       intros accessiblePDChild. simpl.  
(** getTableAddr **)
      eapply WP.bindRev.
      eapply WP.weaken. 
      apply getTableAddr.
      simpl.
      intros s H.
      try repeat rewrite and_assoc in H.
      split.
      pattern s in H. 
      eapply H. subst.
      split. 
      intuition.
      split. 
      instantiate (1:= currentPart). 
      intuition. 
      subst.
      unfold consistency in *. 
      unfold  currentPartitionInPartitionsList in *. 
      intuition.
      instantiate (1:= PDidx).
      split. intuition.
      destruct H as ( _ & _& _ & Hcons & Hlevel  & _ & _ & _ &_ & _& _ & _ & _ & _ &_ & _ & _ & _ &_ & _& Hcp & Hrootpd & H ).
      exists currentPD.
      split. intuition.
      split.
      unfold consistency in *.
      destruct Hcons as (Hpd & _ & _ &_  & Hpr  & _). 
      unfold partitionDescriptorEntry in Hpd.
      assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx\/PDidx = sh3idx\/ PDidx = PPRidx \/ PDidx = PRidx ) as Htmp
          by auto.
      subst.
      generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.     
       generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry).
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx);
       [destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootpd | now contradict Hrootpd | 
       subst ; assumption| now contradict Hrootpd| now contradict Hrootpd ]  |now contradict Hrootpd] | now contradict Hrootpd].

      subst. left. split;intuition.
     intro ptSh1Child. simpl.

 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      Focus 2.
      intros.
      destruct H as (H0 & H1).
      assert(( getTableAddrRoot' ptSh1Child PDidx currentPart shadow1 s /\  ptSh1Child = defaultPage) \/
     (forall idx : index,
      StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
      isPE ptSh1Child idx s/\
     getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s)).
      {
      destruct H1 as [H1 |(Hnew & Hi & H1)].
      + left. trivial. 
      + right. intros idx Hidx.
      
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(_& Hfalse) | [(_&Hfalse) |(Hpe &Htrue)]].
        - contradict Hfalse.
         
       unfold PDidx. unfold sh1idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega.
       - contradict Hfalse.
          unfold PDidx. unfold sh2idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega.
      -split;
       assumption. }
       
       assert (HP := conj H0 H).
       pattern s in HP.
       eapply HP.   
(** comparePageToNull **) 
      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro ptSh1Isnull. simpl.
      case_eq ptSh1Isnull.
      { intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition. }
      intros HptRefChildNotNull. clear HptRefChildNotNull.
(** StateLib.getIndexOfAddr    *)             
      eapply WP.bindRev.
      eapply WP.weaken.
      eapply Invariants.getIndexOfAddr.
      { simpl. intros. 
        destruct H as ((H & [(Hptchild & Hi)| Hptchild]) & Hptchildnotnull).
        + subst. contradict Hptchildnotnull. intro Hnull.  apply beq_nat_false in Hnull. intuition.
        + subst.
          assert (HP := conj (conj H Hptchild) Hptchildnotnull).
(*           try repeat rewrite and_assoc in H. *)
          pattern s in HP.
          eapply HP.  }
       intro idxSh1. simpl.
(**readPresent **)
       eapply WP.bindRev.
       { eapply WP.weaken.
         eapply Invariants.readPresent. simpl.
         intros.
         split. 
(*          try repeat rewrite and_assoc in H. *)
         pattern s in H.
         eapply H. 
         subst.
         destruct H as (H & Hidx).
         assert (forall idx : index,
         StateLib.getIndexOfAddr shadow1 fstLevel = idx -> isPE ptSh1Child idx s /\
     getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s).  
         { intuition. }
         
         apply H0 in Hidx. destruct Hidx; assumption.
       }
       intro presentSh1. simpl.
(**readAccessible **)
       eapply WP.bindRev.
       { eapply WP.weaken.
         eapply Invariants.readAccessible. simpl.
         intros.
         split.
         
(*          try repeat rewrite and_assoc in H. *)
         pattern s in H.
         eapply H. 
         subst.
         apply entryPresentFlagIsPE with presentSh1 ;intuition. }
       intros accessibleSh1. simpl.   
(** getTableAddr **)

      eapply WP.bindRev.
      eapply WP.weaken. 
      apply getTableAddr.
      simpl.
      intros s H.
      try repeat rewrite and_assoc in H.
      split.
      pattern s in H. 
      eapply H. subst.
      split. 
      intuition.
      split. 
      instantiate (1:= currentPart).
      intuition. 
      subst.
      unfold consistency in *. 
      unfold  currentPartitionInPartitionsList in *. 
      intuition.
      instantiate (1:= PDidx).
      split. intuition.
      
      destruct H as ( _ & _& _ & Hcons & Hlevel  & _ & _ & _ &_ & _& _ & 
      b_ & _ & _ &_ & _ & _ & _ &_ & _& Hcp & Hrootpd & H).
      exists currentPD.
      split. intuition.
      split.
      unfold consistency in *.
             destruct Hcons as (Hpd & _ & _ &_  & Hpr  & _). 
      unfold partitionDescriptorEntry in Hpd.
       assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx\/PDidx = sh3idx\/ PDidx = PPRidx \/ PDidx = PRidx ) as Htmp 
          by auto.
          subst.
      generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
      generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry).
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx);
       [destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootpd | now contradict Hrootpd | 
       subst ; assumption| now contradict Hrootpd| now contradict Hrootpd ]  |now contradict Hrootpd] | now contradict Hrootpd].
      subst. left. split;intuition.
      intro ptSh2Child. simpl.
 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      Focus 2.
      intros.
      destruct H as (H0 & H1).
      assert( ( getTableAddrRoot' ptSh2Child PDidx currentPart shadow2 s /\ ptSh2Child = defaultPage) \/
     (forall idx : index,
      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
      isPE ptSh2Child idx s/\
     getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s)).
      {
      destruct H1 as [H1 |(Hi  & Hnew & H1)].
      + left. trivial. 
      + right. intros idx Hidx.
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(_& Hfalse) | [(_&Hfalse) |(Hpe &Htrue)]].
        - contradict Hfalse.
         
       unfold PDidx. unfold sh1idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega.
       - contradict Hfalse.
          unfold PDidx. unfold sh2idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega.
      - split;
       assumption. }
       assert (HP := conj H0 H).
       pattern s in HP.
       eapply HP.  
(** comparePageToNull **) 
      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro ptSh2Isnull. simpl.
      case_eq ptSh2Isnull.
      { intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition. }
      intros HptRefChildNotNull. clear HptRefChildNotNull.
(** StateLib.getIndexOfAddr         *)        
      eapply WP.bindRev.
      eapply WP.weaken.
      eapply Invariants.getIndexOfAddr.
      { simpl. intros. 
        destruct H as ((H & [Hptchild | Hptchild]) & Hptchildnotnull).
        + subst. contradict Hptchildnotnull. intro Hnull. destruct Hptchild.
            apply beq_nat_false in Hnull. subst. intuition.
        + subst.
          assert (HP := conj (conj H Hptchild) Hptchildnotnull).
(*           try repeat rewrite and_assoc in HP. *)
          pattern s in HP.
          eapply HP. }
       intro idxSh2. simpl.
(**readPresent **)
       eapply WP.bindRev.
       { eapply WP.weaken.
         eapply Invariants.readPresent. simpl.
         intros.
         split.
(*          try repeat rewrite and_assoc in H. *)
         pattern s in H.
         eapply H. 
         subst.
         destruct H as (H & Hidx).
         assert (forall idx : index,
         StateLib.getIndexOfAddr shadow2 fstLevel = idx -> isPE ptSh2Child idx s /\
     getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s).  
         { intuition. }
         
         apply H0 in Hidx. destruct Hidx;assumption.
       }
       intro presentSh2. simpl.
(**readAccessible **)
       eapply WP.bindRev.
       { eapply WP.weaken.
         eapply Invariants.readAccessible. simpl.
         intros.
         split.
(*          try repeat rewrite and_assoc in H. *)
         pattern s in H.
         eapply H. 
         subst.
         apply entryPresentFlagIsPE with presentSh2 ;intuition. }
       intros accessibleSh2. simpl.
(** getTableAddr **)
      eapply WP.bindRev.
      eapply WP.weaken. 
      apply getTableAddr.
      simpl.
      intros s H.
      try repeat rewrite and_assoc in H.
      split.
      pattern s in H. 
      eapply H. subst.
      split. 
      intuition.
      split. 
      instantiate (1:= currentPart).
      intuition. 
      subst.
      unfold consistency in *. 
      unfold  currentPartitionInPartitionsList in *. 
      intuition.
      instantiate (1:= PDidx).
      split. intuition.
      destruct H as ( _ & _& _ & Hcons & Hlevel  & _ & _ & _ &_ & _& _ & _ & _ & _ &_ & _ & _ & _ &_ & _& Hcp & Hrootpd & H ).

      exists currentPD.
      split. intuition.
      split.
      unfold consistency in *.
      destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
      unfold partitionDescriptorEntry in Hpd.
      assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx\/ PDidx = sh3idx
       \/ PDidx = PPRidx \/ PDidx = PRidx) as Htmp 
      by auto.
            generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
      generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry). 
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx);
       [destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootpd | now contradict Hrootpd | 
       subst ; assumption| now contradict Hrootpd| now contradict Hrootpd ]  |now contradict Hrootpd] | now contradict Hrootpd].

      subst. left. split;intuition.
      intro ptConfigPagesList. simpl.
 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      Focus 2.
      intros.
      destruct H as (H0 & H1).
       assert( ( getTableAddrRoot' ptConfigPagesList PDidx currentPart list s /\ ptConfigPagesList = defaultPage) \/
     (forall idx : index,
      StateLib.getIndexOfAddr list fstLevel = idx ->
      isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList PDidx currentPart list s)).
      {
      destruct H1 as [H1 |(Hi & Hi1 &H1)].
      + left. trivial. 
      + right. intros idx Hidx.
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(_& Hfalse) | [(_&Hfalse) |(Hpe &Htrue)]].
        - contradict Hfalse.
         
       unfold PDidx. unfold sh1idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega.
       - contradict Hfalse.
          unfold PDidx. unfold sh2idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega.
      - split;
       assumption. }
    assert (HP := conj H0 H).
    pattern s in HP.
    eapply HP.
(** comparePageToNull **) 
      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro ptConfigPagesListIsnull. simpl.
      case_eq ptConfigPagesListIsnull.
      { intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition. }
      intros HptRefChildNotNull. clear HptRefChildNotNull.
(** getIndexOfAddr *)                 
      eapply WP.bindRev.
      eapply WP.weaken.
      eapply Invariants.getIndexOfAddr.
      { simpl. intros. 
        destruct H as ((H & [Hptchild | Hptchild]) & Hptchildnotnull).
        + destruct Hptchild. subst. contradict Hptchildnotnull.
          intro Hnull.  apply beq_nat_false in Hnull. intuition.
        + subst.
          assert (HP := conj (conj H Hptchild) Hptchildnotnull).
(*           try repeat rewrite and_assoc in HP. *)
          pattern s in HP.
          eapply HP. }
       intro idxConfigPagesList. simpl.
(**readPresent **)
       eapply WP.bindRev.
       { eapply WP.weaken.
         eapply Invariants.readPresent. simpl.
         intros.
         split.
(*          try repeat rewrite and_assoc in H. *)
         pattern s in H.
         eapply H. 
         subst.
         destruct H as (H & Hidx).
         assert (forall idx : index,
         StateLib.getIndexOfAddr list fstLevel = idx -> isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList PDidx currentPart list s).  
         { intuition. }
         
         apply H0 in Hidx. destruct Hidx;assumption.
       }
       intro presentConfigPagesList. simpl.
(**readAccessible **)
       eapply WP.bindRev.
       { eapply WP.weaken.
         eapply Invariants.readAccessible. simpl.
         intros.
         split.
(*          try repeat rewrite and_assoc in H. *)
         pattern s in H.
         eapply H. 
         subst.
         apply entryPresentFlagIsPE with presentConfigPagesList ;intuition. }
      intros accessibleList. simpl.    
(** case present && accessible **)
      case_eq (presentRefChild && accessibleChild && presentPDChild && accessiblePDChild &&
               presentConfigPagesList && accessibleList && presentSh1 && accessibleSh1 && 
               presentSh2 && accessibleSh2).
(** fst case : accessible and present **)
      { intro Hlegit.
(** getFstShadow **)
      eapply WP.bindRev.
        { eapply WP.weaken. 
            eapply Invariants.getFstShadow. cbn.
            intros s H.
            split.
(*              try repeat rewrite and_assoc in H.  *)
            pattern s in H.
            eapply H.
            unfold consistency in *.
           unfold partitionDescriptorEntry in *.
          intuition.   }
      intro currentShadow1.
(** getTableAddr **)
      eapply WP.bindRev.
      eapply WP.weaken. 
      apply getTableAddr.
      simpl.
      intros s H.
      split.
(*       try repeat rewrite and_assoc in H. *)
      
      pattern s in H. 
      eapply H. subst.
      split. 
      intuition.
      split. 
      instantiate (1:= currentPart).
      intuition. 
      subst.
      unfold consistency in *. 
      unfold  currentPartitionInPartitionsList in *. 
      intuition.
      instantiate (1:= sh1idx).
      split. intuition. (*
      destruct H as ( (_ & _& _ & Hcons & Hlevel  & _ & _ & _ &_ & _& 
      _ & _ & _ & _ &_ & _ & _ & _ &_ & _& Hcp & Hrootpd & H) & H0). *)
      assert(Hcons : consistency s) by intuition.
      assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
      assert (Hrootpd : nextEntryIsPP currentPart PDidx currentPD s) by intuition.
      assert(Hcp : currentPart = currentPartition s) by intuition.
      assert (H0 : nextEntryIsPP currentPart sh1idx currentShadow1 s) by intuition.
      exists currentShadow1.
      split. intuition.
      unfold consistency in *.
      destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
      unfold partitionDescriptorEntry in Hpd.
      assert (sh1idx = PDidx \/ sh1idx = sh1idx \/ sh1idx = sh2idx 
      \/  sh1idx  = sh3idx \/ sh1idx  = PPRidx \/  sh1idx = PRidx) as Htmp 
      by auto.
          generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
      generalize (Hpd sh1idx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry). 
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      split.     
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ sh1idx);
       [destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootpd | 
       now contradict Hrootpd | 
       subst;assumption | now contradict Hrootpd| now contradict Hrootpd ]  
       |now contradict Hrootpd] | now contradict Hrootpd].
      subst. left. split;intuition.
      intro ptRefChildFromSh1.
      simpl.
 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      Focus 2.
      intros.
      destruct H as (H0 & H1).
      assert ( (getTableAddrRoot' ptRefChildFromSh1 sh1idx currentPart descChild s /\ ptRefChildFromSh1 = defaultPage) \/
     (forall idx : index,
      StateLib.getIndexOfAddr descChild fstLevel = idx ->
      isVE ptRefChildFromSh1 idx s /\  getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s)).
      { destruct H1 as [H1 |(Hi & Hi1 & H1 )].
      + left. trivial. 
      + right. intros idx Hidx.
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(Hpe &Htrue) |[ (_& Hfalse) | (_&Hfalse) ]].
        - split; assumption.
        - contradict Hfalse.
         
       unfold sh2idx. unfold sh1idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega.
       - contradict Hfalse.
          unfold PDidx. unfold sh1idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega. }
    assert (HP := conj H0 H).
    pattern s in HP.
    eapply HP. 
(** comparePageToNull **) 
      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro ptRefChildFromSh1Isnull. simpl.
      case_eq ptRefChildFromSh1Isnull.
      { intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition. }
      intros HptRefChildNotNull. clear HptRefChildNotNull.
      
(** derived **)
      eapply WP.bindRev.
      { eapply WP.weaken.
        eapply Invariants.checkDerivation. simpl.
        simpl. intros. 
        destruct H as ((H & [Hptchild | Hptchild]) & Hptchildnotnull).
        + destruct Hptchild. subst. contradict Hptchildnotnull.
          intro Hnull.  apply beq_nat_false in Hnull. intuition.
        + subst.
          assert (HP := conj (conj H Hptchild) Hptchildnotnull).
(*           try repeat rewrite and_assoc in HP. *)
          split.
          eapply HP. 
          subst.
          assert ( StateLib.getIndexOfAddr descChild fstLevel = idxRefChild) as Hidxchild.
          intuition.
          apply Hptchild in Hidxchild. destruct Hidxchild; assumption. }
      simpl. intros derivedRefChild.
(** getTableAddr **)
      eapply WP.bindRev.
      eapply WP.weaken. 
      apply getTableAddr.
      simpl.
      intros s H.
(*       try repeat rewrite and_assoc in H. *)
      split.
(*       try repeat rewrite and_assoc in H. *)
      pattern s in H. 
      eapply H. subst.
      split. 
      intuition.
      split. 
      instantiate (1:= currentPart). 
      intuition. 
      subst.
      unfold consistency in *. 
      unfold  currentPartitionInPartitionsList in *. 
      intuition.
      instantiate (1:= sh1idx).
      split. intuition.
      assert(Hcons : consistency s) by intuition.
      assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
      assert (Hrootpd : nextEntryIsPP currentPart PDidx currentPD s) by intuition.
      assert(Hcp : currentPart = currentPartition s) by intuition.
      assert (H0 : nextEntryIsPP currentPart sh1idx currentShadow1 s) by intuition.
      (*
      destruct H as ( _ & _& _ & Hcons & Hlevel  & _ & _ & _ &_ & _& _ & _ & _ & _ &_ & _ & _ & _ &_ & _& Hcp & Hrootpd & H ).
      assert (nextEntryIsPP currentPart sh1idx currentShadow1 s ). intuition. *)
      exists currentShadow1.
      split. intuition.
      unfold consistency in *.

        destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
      unfold partitionDescriptorEntry in Hpd.
      assert (sh1idx = PDidx \/ sh1idx = sh1idx \/ sh1idx = sh2idx \/  sh1idx  = sh3idx
      \/  sh1idx  = PPRidx \/  sh1idx = PRidx) as Htmp 
      by auto.
          generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
      generalize (Hpd sh1idx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry). 
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      split.     
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ sh1idx);
       [destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootpd | 
       now contradict Hrootpd | 
       subst;assumption | now contradict Hrootpd| now contradict Hrootpd ]  
       |now contradict Hrootpd] | now contradict Hrootpd].
      subst. left. split;intuition.
      intro ptPDChildSh1. simpl.
 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      Focus 2.
      intros.
      destruct H as (H0 & H1).
          
      assert (  (getTableAddrRoot' ptPDChildSh1 sh1idx currentPart pdChild s /\ ptPDChildSh1 = defaultPage) \/
     (forall idx : index,
      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
      isVE ptPDChildSh1 idx s /\
     getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s )).
      { destruct H1 as [H1 |( Hi & Hi1  &H1 )].
      + left. trivial. 
      + right. intros idx Hidx.
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(Hpe &Htrue) |[ (_& Hfalse) | (_&Hfalse) ]].
        - split; assumption.
        - contradict Hfalse.
          unfold sh2idx. unfold sh1idx.
          apply indexEqFalse;
          assert (tableSize > tableSizeLowerBound).
          apply tableSizeBigEnough.
          unfold tableSizeLowerBound in *.
          omega.  apply tableSizeBigEnough.
          unfold tableSizeLowerBound in *.
          omega. apply tableSizeBigEnough. omega.
           - contradict Hfalse.
             unfold PDidx. unfold sh1idx.
             apply indexEqFalse;
             assert (tableSize > tableSizeLowerBound).
             apply tableSizeBigEnough.
             unfold tableSizeLowerBound in *.
             omega.  apply tableSizeBigEnough.
             unfold tableSizeLowerBound in *.
             omega. apply tableSizeBigEnough. omega. }
    assert (HP := conj H0 H).
    pattern s in HP.
    eapply HP.
(** comparePageToNull **) 

      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro ptPDChildSh1Isnull. simpl.

      case_eq ptPDChildSh1Isnull.
      { intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition. }
      intros HptRefChildNotNull. clear HptRefChildNotNull.
      
(** derived **)
      eapply WP.bindRev.
      {  eapply WP.weaken.
        eapply Invariants.checkDerivation. simpl.
        simpl. intros. 
        destruct H as ((H & [Hptchild | Hptchild]) & Hptchildnotnull).
        +  destruct Hptchild. subst. contradict Hptchildnotnull.
          intro Hnull.  apply beq_nat_false in Hnull. intuition.
        + subst.
          assert (HP := conj (conj H Hptchild) Hptchildnotnull).
(*           try repeat rewrite and_assoc in HP. *)
          split.
          eapply HP. 
          subst.
          assert ( StateLib.getIndexOfAddr pdChild fstLevel = idxPDChild) as Hidxchild.
          intuition. 
          apply Hptchild in Hidxchild. destruct Hidxchild;assumption. }
      simpl. intros derivedPDChild.
(** getTableAddr **)
      eapply WP.bindRev.
      eapply WP.weaken. 
      apply getTableAddr.
      simpl.
      intros s H.
    (*   try repeat rewrite and_assoc in H. *)
      split.
(*       try repeat rewrite and_assoc in H. *)
      pattern s in H. 
      eapply H. subst.
      split. 
      intuition.
      split. 
      instantiate (1:= currentPart).
      intuition. 
      subst.
      unfold consistency in *. 
      unfold  currentPartitionInPartitionsList in *. 
      intuition.
      instantiate (1:= sh1idx).
      split. intuition.
      assert(Hcons : consistency s) by intuition.
      assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
      assert (Hrootpd : nextEntryIsPP currentPart PDidx currentPD s) by intuition.
      assert(Hcp : currentPart = currentPartition s) by intuition.
      assert (H0 : nextEntryIsPP currentPart sh1idx currentShadow1 s) by intuition.
      (*
      destruct H as ( _ & _& _ & Hcons & Hlevel  & _ & _ & _ &_ & _& _ & _ & _ 
      & _ &_ & _ & _ & _ &_ & _& Hcp & Hrootpd & H ).
      assert (nextEntryIsPP currentPart sh1idx currentShadow1 s ). intuition. *)
      exists currentShadow1.
      split. intuition.
      unfold consistency in *.
        destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
      unfold partitionDescriptorEntry in Hpd.
      assert (sh1idx = PDidx \/ sh1idx = sh1idx \/ sh1idx = sh2idx \/  sh1idx  = sh3idx
      \/  sh1idx  = PPRidx \/  sh1idx = PRidx) as Htmp 
      by auto.
          generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
      generalize (Hpd sh1idx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry). 
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      split.     
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ sh1idx);
       [destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootpd | 
       now contradict Hrootpd | 
       subst;assumption | now contradict Hrootpd| now contradict Hrootpd ]  
       |now contradict Hrootpd] | now contradict Hrootpd].
      subst. left. split;intuition.
      intro ptSh1ChildFromSh1. simpl.
 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      Focus 2.
      intros.
      destruct H as (H0 & H1).
      assert ( (getTableAddrRoot' ptSh1ChildFromSh1 sh1idx currentPart shadow1 s /\  ptSh1ChildFromSh1 = defaultPage) \/
     (forall idx : index,
      StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
      isVE ptSh1ChildFromSh1 idx s /\ getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s)).
      { destruct H1 as [H1 |(Hi & Hi1 &H1)].
      + left. trivial. 
      + right. intros idx Hidx.
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(Hpe &Htrue) |[ (_& Hfalse) | (_&Hfalse) ]].
        - split; assumption.
        - contradict Hfalse.
         
       unfold sh2idx. unfold sh1idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega.
       - contradict Hfalse.
          unfold PDidx. unfold sh1idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega. }
    assert (HP := conj H0 H).
    pattern s in HP.
    eapply HP.
(** comparePageToNull **) 

      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro childSh1Isnull. simpl.

      case_eq childSh1Isnull.
      { intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition. }
      intros HptRefChildNotNull. clear HptRefChildNotNull.
      
(** derived **)
      eapply WP.bindRev.
      { eapply WP.weaken.
        eapply Invariants.checkDerivation. simpl.
        simpl. intros. 
        destruct H as ((H & [Hptchild | Hptchild]) & Hptchildnotnull).
        + destruct Hptchild. subst. contradict Hptchildnotnull.
          intro Hnull.  apply beq_nat_false in Hnull. intuition.
        + subst.
          assert (HP := conj (conj H Hptchild) Hptchildnotnull).
(*           try repeat rewrite and_assoc in HP. *)
          split.
          eapply HP. 
          subst.
          assert ( StateLib.getIndexOfAddr shadow1 fstLevel = idxSh1) as Hidxchild.
          intuition.
          apply Hptchild in Hidxchild. destruct Hidxchild.
          assumption. }
      simpl. intros derivedSh1Child.
(** getTableAddr **)
      eapply WP.bindRev.
      eapply WP.weaken. 
      apply getTableAddr.
      simpl.
      intros s H.
(*       try repeat rewrite and_assoc in H. *)
      split.
(*       try repeat rewrite and_assoc in H. *)
      pattern s in H. 
      eapply H. subst.
      split. 
      intuition.
      split. 
      instantiate (1:= currentPart). 
      intuition. 
      subst.
      unfold consistency in *. 
      unfold  currentPartitionInPartitionsList in *. 
      intuition.
      instantiate (1:= sh1idx).
      split. intuition.
      assert(Hcons : consistency s) by intuition.
      assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
      assert (Hrootpd : nextEntryIsPP currentPart PDidx currentPD s) by intuition.
      assert(Hcp : currentPart = currentPartition s) by intuition.
      assert (H0 : nextEntryIsPP currentPart sh1idx currentShadow1 s) by intuition.
      (*
      destruct H as ( _ & _& _ & Hcons & Hlevel  & _ & _ & _ &_ & _& _ & _ 
      & _ & _ &_ & _ & _ & _ &_ & _& Hcp & Hrootpd & H).
      assert (nextEntryIsPP currentPart sh1idx currentShadow1 s ). intuition.*)
      exists currentShadow1.
      split. intuition.
      unfold consistency in *.
              destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
      unfold partitionDescriptorEntry in Hpd.
      assert (sh1idx = PDidx \/ sh1idx = sh1idx \/ sh1idx = sh2idx \/  sh1idx  = sh3idx
      \/  sh1idx  = PPRidx \/  sh1idx = PRidx) as Htmp 
      by auto.
          generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
      generalize (Hpd sh1idx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry). 
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      split.     
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ sh1idx);
       [destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootpd | 
       now contradict Hrootpd | 
       subst;assumption | now contradict Hrootpd| now contradict Hrootpd ]  
       |now contradict Hrootpd] | now contradict Hrootpd].
      subst. left. split;intuition.
      intro childSh2. simpl.
 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      Focus 2.
      intros.
      destruct H as (H0 & H1).
      assert (  (getTableAddrRoot' childSh2 sh1idx currentPart shadow2 s /\ childSh2 = defaultPage) \/
     (forall idx : index,
      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
      isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s )).
      { destruct H1 as [H1 |(Hi & Hi1 &H1)].
      + left. trivial. 
      + right. intros idx Hidx.
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(Hpe &Htrue) |[ (_& Hfalse) | (_&Hfalse) ]].
        - split; assumption.
        - contradict Hfalse.
         
       unfold sh2idx. unfold sh1idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega.
       - contradict Hfalse.
          unfold PDidx. unfold sh1idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega. }
    assert (HP := conj H0 H).
    pattern s in HP.
    eapply HP.
(** comparePageToNull **) 

      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro childSh2Isnull. simpl.

      case_eq childSh2Isnull.
      { intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition. }
      intros HptRefChildNotNull. clear HptRefChildNotNull.
      
(** derived **)
      eapply WP.bindRev.
      { eapply WP.weaken.
        eapply Invariants.checkDerivation. simpl.
        simpl. intros. 
        destruct H as ((H & [Hptchild | Hptchild]) & Hptchildnotnull).
        + destruct Hptchild. subst. contradict Hptchildnotnull.
          intro Hnull.  apply beq_nat_false in Hnull. intuition.
        + subst.
          assert (HP := conj (conj H Hptchild) Hptchildnotnull).
(*           try repeat rewrite and_assoc in HP. *)
          split.
          eapply HP. 
          subst.
          assert ( StateLib.getIndexOfAddr shadow2 fstLevel = idxSh2) as Hidxchild.
          intuition. 
          apply Hptchild in Hidxchild. destruct Hidxchild; assumption. }
      simpl. intros derivedSh2Child.


(** getTableAddr **)
      eapply WP.bindRev.
      eapply WP.weaken. 
      apply getTableAddr.
      simpl.
      intros s H.
(*       try repeat rewrite and_assoc in H. *)
      split.
(*       try repeat rewrite and_assoc in H.  *)
      pattern s in H. 
      eapply H. subst.
      split. 
      intuition.
      split. 
      instantiate (1:= currentPart).
      intuition. 
      subst.
      unfold consistency in *. 
      unfold  currentPartitionInPartitionsList in *. 
      intuition.
      instantiate (1:= sh1idx).
      split. intuition.
      assert(Hcons : consistency s) by intuition.
      assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
      assert (Hrootpd : nextEntryIsPP currentPart PDidx currentPD s) by intuition.
      assert(Hcp : currentPart = currentPartition s) by intuition.
      assert (H0 : nextEntryIsPP currentPart sh1idx currentShadow1 s) by intuition.
      (*
      destruct H as ( _ & _& _ & Hcons & Hlevel  & _ & _ & _ &_ & _& 
      _ & _ & _ & _ &_ & _ & _ & _ &_ & _& Hcp & Hrootpd & H ).
      assert (nextEntryIsPP currentPart sh1idx currentShadow1 s ). intuition. *)
      exists currentShadow1.
      split. intuition.
      unfold consistency in *.
      
              destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
      unfold partitionDescriptorEntry in Hpd.
      assert (sh1idx = PDidx \/ sh1idx = sh1idx \/ sh1idx = sh2idx \/  sh1idx  = sh3idx
      \/  sh1idx  = PPRidx \/  sh1idx = PRidx) as Htmp 
      by auto.
          generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
      generalize (Hpd sh1idx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry). 
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      split.     
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ sh1idx);
       [destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootpd | 
       now contradict Hrootpd | 
       subst;assumption | now contradict Hrootpd| now contradict Hrootpd ]  
       |now contradict Hrootpd] | now contradict Hrootpd].
      subst. left. split;intuition.
      intro childListSh1. simpl.
 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      Focus 2.
      intros.
      destruct H as (H0 & H1).
      assert ( (getTableAddrRoot' childListSh1 sh1idx currentPart list s /\ childListSh1 = defaultPage) \/
     (forall idx : index,
      StateLib.getIndexOfAddr list fstLevel = idx ->
      isVE childListSh1 idx s /\ getTableAddrRoot childListSh1 sh1idx currentPart list s  )).
      { destruct H1 as [H1 |(Hi & Hi1 & H1)].
      + left. trivial. 
      + right. intros idx Hidx.
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(Hpe &Htrue) |[ (_& Hfalse) | (_&Hfalse) ]].
        - split; assumption.
        - contradict Hfalse.
         
       unfold sh2idx. unfold sh1idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega.
       - contradict Hfalse.
          unfold PDidx. unfold sh1idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega. }
    assert (HP := conj H0 H).
    pattern s in HP.
    eapply HP.
(** comparePageToNull **) 

      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro childListSh1Isnull. simpl.

      case_eq childListSh1Isnull.
      { intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition. }
      intros HptRefChildNotNull. clear HptRefChildNotNull.
      
(** derived **)
      eapply WP.bindRev.
      { eapply WP.weaken.
        eapply Invariants.checkDerivation. simpl.
        simpl. intros. 
        destruct H as ((H & [Hptchild | Hptchild]) & Hptchildnotnull).
        + destruct Hptchild. subst. contradict Hptchildnotnull.
          intro Hnull.  apply beq_nat_false in Hnull. intuition.
        + subst.
          assert (HP := conj (conj H Hptchild) Hptchildnotnull).
(*           try repeat rewrite and_assoc in HP.  *)
          split.
          eapply HP. 
          subst.
          assert ( StateLib.getIndexOfAddr list fstLevel = idxConfigPagesList) as Hidxchild.
          intuition.  
          apply Hptchild in Hidxchild. destruct Hidxchild; assumption.  }
      simpl. intros derivedRefChildListSh1.
(** Derivation Test **) 
    case_eq ( derivedRefChild && derivedPDChild && derivedSh1Child && derivedSh2Child && derivedRefChildListSh1).
    - intros. 
(** readPhyEntry **)
    eapply WP.bindRev.
    eapply WP.weaken.  
    eapply Invariants.readPhyEntry.
    simpl. intros.
    split.
    pattern s in H0.
    eapply H0. 
    subst.
    unfold propagatedProperties in *.
    assert (Hpe : forall idx : index,
      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
      isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by intuition.
    apply Hpe.
    intuition.
    simpl.
    intros phyPDChild.
(** comparePageToNull **) 
    eapply WP.bindRev.
    eapply Invariants.comparePageToNull.
    intro phyPDChildIsnull.
    simpl.
    case_eq phyPDChildIsnull.
    { intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition. }
    intros phyPDChildNotNull.    
(** readPhyEntry **)
    eapply WP.bindRev.
    eapply WP.weaken.  
    eapply Invariants.readPhyEntry.
    simpl. intros.
    split. 
    assert(Hphy : forall partition, In partition (getPartitions multiplexer s) ->
    ~ In phyPDChild (getConfigPages partition s) ).
    { intros. try repeat rewrite  andb_true_iff in Hlegit.
      try repeat rewrite and_assoc in Hlegit.
      destruct Hlegit as (_ & _ & presentPD & accessPD & _).
       unfold  consistency in *.
      assert (Hcurpart : currentPartitionInPartitionsList s) by intuition.
      unfold currentPartitionInPartitionsList in *; trivial. 
      assert (Hkernel : kernelDataIsolation s) by intuition.
      unfold kernelDataIsolation in Hkernel.
      unfold disjoint in Hkernel.
      apply Hkernel with (currentPartition s); trivial.
      intuition.
      apply physicalPageIsAccessible with ptPDChild pdChild idxPDChild 
      accessiblePDChild level presentPDChild currentPD; subst; intuition.
    }
(*     assert(HpdChildaccess : getAccessibleMappedPage currentPD s pdChild = Some phyPDChild).
    
    { apply isAccessibleMappedPage. SearchAbout getAccessibleMappedPage. apply accessibleMappedPagesInMappedPages.
      assert(Hinaccess : In phyPDChild (getAccessibleMappedPages currentPart s)).
      intuition.
      repeat rewrite andb_true_iff in Hlegit.
      intuition.
      apply physicalPageIsAccessible with ptPDChild pdChild idxPDChild
      accessiblePDChild level presentPDChild currentPD;trivial.
      subst;trivial.
      subst.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *;intuition.
      accessi

    assert(Hcurpart : In currentPart (getPartitions multiplexer s)) by admit.
    assert(Hcurpd : StateLib.getPd currentPart (memory s) = Some currentPD) by admit.
    assert(Hparent : exists parent , getParent currentPart (memory s) = Some parent ) 
    by admit.
    assert(Hsh2 :exists currentSh2, getSndShadow currentPart (memory s) = Some currentSh2)
     by admit.
    destruct Hsh2 as (currentSh2 & Hsh2).
    assert(HvaInParent : exists vaInParent, getVirtualAddressSh2 currentSh2 s pdChild = 
    Some vaInParent) by admit.
    destruct Hparent as (parent & Hparent).
    assert(HpdParent: exists pdParent, StateLib.getPd parent (memory s) = Some pdParent)
    by admit.
    destruct HvaInParent as (vaInParent & HvaInParent).
    destruct HpdParent as (pdParent & HpdParent).
    assert(HaccessInparent : getAccessibleMappedPage pdParent s vaInParent =
    Some phyPDChild).
    { intuition. subst.
      unfold consistency in *.
      assert(Haccess : accessibleChildPhysicalPageIsAccessibleIntoParent s) by intuition.
      unfold accessibleChildPhysicalPageIsAccessibleIntoParent in *.  
      apply Haccess with (currentPartition s) pdChild currentPD parent currentSh2;trivial. }  *)   
    assert(Hnew := conj H0 Hphy).    
(*     assert(Hnew' := conj Hnew HaccessInparent). *)
    pattern s in Hnew.
    apply Hnew. 
    subst.
    unfold propagatedProperties in *.
    assert (Hpe : forall idx : index,
                   StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                   isPE ptSh1Child idx s /\ getTableAddrRoot ptSh1Child PDidx 
                   currentPart shadow1 s) by intuition.
    apply Hpe.
    intuition.
    simpl.
    intros phySh1Child.
(** comparePageToNull **) 
    eapply WP.bindRev.
    eapply Invariants.comparePageToNull.
    intro phySh1ChildIsnull.
    simpl.
    case_eq phySh1ChildIsnull.
    { intros.
      eapply WP.weaken.
      eapply WP.ret .
      simpl.
      intros.
      intuition. }
    intros phySh1ChildNotNull.
(** readPhyEntry **)
    eapply WP.bindRev.
    eapply WP.weaken.  
    eapply Invariants.readPhyEntry.
    simpl. intros.
    split.
    assert(Hphy : forall partition, In partition (getPartitions multiplexer s) -> 
    ~ In phySh1Child  (getConfigPages partition s) ).
    { intros. try repeat rewrite  andb_true_iff in Hlegit.
      try repeat rewrite and_assoc in Hlegit.
      destruct Hlegit as (_ & _ & _ & _ & _ & _ &  presentPD & accessPD & _).
      unfold  consistency in *.
      assert (Hcurpart : currentPartitionInPartitionsList s) by intuition.
      unfold currentPartitionInPartitionsList in *; trivial.
      assert (Hkernel : kernelDataIsolation s) by intuition.
      unfold kernelDataIsolation in Hkernel.
      unfold disjoint in Hkernel.
      apply Hkernel with (currentPartition s); trivial.
      intuition.
      apply physicalPageIsAccessible with ptSh1Child shadow1 idxSh1 accessibleSh1
       level presentSh1 currentPD ; subst;intuition . }
    assert(Hnew := conj H0 Hphy).    
    pattern s in Hnew.
    eapply Hnew. 
    subst.
    unfold propagatedProperties in *.
    assert (Hpe : forall idx : index,
                     StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                     isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child 
                     PDidx currentPart shadow2 s) by intuition.
    apply Hpe.
    intuition. 
    simpl.
    intros phySh2Child.
(** comparePageToNull **) 
    eapply WP.bindRev.
    eapply Invariants.comparePageToNull.
    intro phySh2ChildIsnull.
    simpl.
    case_eq phySh2ChildIsnull.
    { intros.
      eapply WP.weaken.
      eapply WP.ret .
      simpl.
      intros.
      intuition. }
    intros phySh2ChildNotNull.
(** readPhyEntry **)
    eapply WP.bindRev.
    eapply WP.weaken.  
    eapply Invariants.readPhyEntry.
    simpl. intros.
    split.
    assert(Hphy : forall partition, In partition (getPartitions multiplexer s) ->
    ~ In phySh2Child (getConfigPages partition s)).
    { intros. try repeat rewrite  andb_true_iff in Hlegit.
      try repeat rewrite and_assoc in Hlegit.
      destruct Hlegit as (_ & _ & _ & _ & _ & _ & _ & _ &  presentPD & accessPD ).
      unfold  consistency in *.
      assert (Hcurpart : currentPartitionInPartitionsList s) by intuition.
      unfold currentPartitionInPartitionsList in *; trivial.
      assert (Hkernel : kernelDataIsolation s) by intuition.
      unfold kernelDataIsolation in Hkernel.
      unfold disjoint in Hkernel.
      apply Hkernel with (currentPartition s); trivial.
      intuition.
      apply physicalPageIsAccessible with ptSh2Child shadow2 idxSh2 accessibleSh2
       level presentSh2 currentPD ; subst;intuition. }
    assert(Hnew := conj H0 Hphy).    
    pattern s in Hnew.
    eapply Hnew. 
    subst.
    unfold propagatedProperties in *.
    assert (Hpe : forall idx : index,
                       StateLib.getIndexOfAddr list fstLevel = idx ->
                       isPE ptConfigPagesList idx s /\
                       getTableAddrRoot ptConfigPagesList PDidx currentPart list s) 
    by intuition.
    apply Hpe.
    intuition.
    simpl.
    intros phyConfigPagesList.
(** comparePageToNull **) 
    eapply WP.bindRev.
    eapply Invariants.comparePageToNull.
    intro phyConfigPagesListIsnull.
    simpl.
    case_eq phyConfigPagesListIsnull.
    { intros.
      eapply WP.weaken.
      eapply WP.ret .
      simpl.
      intros.
      intuition. }
    intros phyConfigPagesListNotNull.
(** readPhyEntry **)
    eapply WP.bindRev.
    eapply WP.weaken.  
    eapply Invariants.readPhyEntry.
    simpl. intros.
    split.
    assert(Hphy : forall partition, In partition (getPartitions multiplexer s) ->
    ~ In phyConfigPagesList (getConfigPages partition s)).
    { intros. try repeat rewrite  andb_true_iff in Hlegit.
      try repeat rewrite and_assoc in Hlegit.
      destruct Hlegit as (_ & _ & _ & _ & presentPD & accessPD & _ ).
       unfold  consistency in *.
      assert (Hcurpart : currentPartitionInPartitionsList s) by intuition.
      unfold currentPartitionInPartitionsList in *; trivial.
      assert (Hkernel : kernelDataIsolation s) by intuition.
      unfold kernelDataIsolation in Hkernel.
      unfold disjoint in Hkernel.
      apply Hkernel with (currentPartition s); trivial.
      intuition.
      apply physicalPageIsAccessible with ptConfigPagesList list idxConfigPagesList 
      accessibleList level presentConfigPagesList currentPD; subst;intuition. }
    assert(Hnew := conj H0 Hphy).    
    pattern s in Hnew.
    eapply Hnew. 
    subst.
    unfold propagatedProperties in *.
    assert (Hpe : forall idx : index,
                         StateLib.getIndexOfAddr descChild fstLevel = idx ->
                         isPE ptRefChild idx s /\
                         getTableAddrRoot ptRefChild PDidx currentPart descChild s)
    by intuition.
    apply Hpe.
    intuition.
    simpl.
    intros phyDescChild.
(** comparePageToNull **) 
    eapply WP.bindRev.
    eapply Invariants.comparePageToNull.
    intro phyDescChildIsnull.
    simpl.
    case_eq phyDescChildIsnull.
    { intros.
      eapply WP.weaken.
      eapply WP.ret .
      simpl.
      intros.
      intuition. }
    intros phyDescChildNotNull.
(** writeAccessible : pdChild **)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply WP.writeAccessible.
    intros. simpl.
    assert (exists entry : Pentry,
      lookup ptPDChild idxPDChild (memory s) beqPage beqIndex = Some (PE entry)) as Hlookup.
    { apply isPELookupEq.
      assert (forall idx : index,
          StateLib.getIndexOfAddr pdChild fstLevel = idx ->
          isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild PDidx currentPart pdChild s) as H1 by intuition.
      generalize (H1  idxPDChild);clear H1; intros H1.
      assert (StateLib.getIndexOfAddr pdChild fstLevel = idxPDChild ) as H2 by intuition.
      apply H1 in H2. intuition. }      
    destruct Hlookup as (entry & Hlookup).
    exists entry ; split;trivial.

    assert(Hphy :forall partition, In partition (getPartitions multiplexer s) ->
      ~ In phyDescChild  (getConfigPages partition s)).
    { intros. 
      try repeat rewrite  andb_true_iff in Hlegit.
      try repeat rewrite and_assoc in Hlegit.
      destruct Hlegit as ( presentPD & accessPD & _ ).
       unfold  consistency in *.
      assert (Hcurpart : currentPartitionInPartitionsList s) by intuition.
      unfold currentPartitionInPartitionsList in *; trivial.
      assert (Hkernel : kernelDataIsolation s) by intuition.
      unfold kernelDataIsolation in Hkernel.
      unfold disjoint in Hkernel.
      apply Hkernel with (currentPartition s); trivial.
      intuition.
      apply physicalPageIsAccessible with ptRefChild descChild 
      idxRefChild accessibleChild level presentRefChild currentPD; subst; intuition. }
    assert (Hreadflag : isPartitionFalse ptPDChildSh1 idxPDChild s ).
   { unfold isPartitionFalse.
    unfold consistency in *. 
    assert(Haccessva : accessibleVAIsNotPartitionDescriptor s) by intuition.
    unfold accessibleVAIsNotPartitionDescriptor in *.
    assert (Hflag : getPDFlag currentShadow1 pdChild s = false).
    { apply Haccessva with currentPart currentPD phyPDChild.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      subst;assumption.
      apply nextEntryIsPPgetPd; intuition.
      apply nextEntryIsPPgetFstShadow;intuition.
      assert (pa entry = phyPDChild).
      apply isEntryPageLookupEq with ptPDChild idxPDChild s; trivial.
      intuition.
      subst.
      repeat rewrite andb_true_iff in Hlegit.
      intuition.
      subst.      
      apply isAccessibleMappedPage with ptPDChild;trivial. }
    apply getPDFlagReadPDflag with currentShadow1 pdChild currentPart;trivial.
    intuition.  
    apply Nat.eqb_neq.
    assert(Hfalsepge : (defaultPage =? ptPDChildSh1) = false) by trivial.
    apply beq_nat_false in Hfalsepge.
    unfold not;intros Hfalse'.
    rewrite Hfalse' in Hfalsepge.    
    now contradict Hfalsepge.
    intuition.
    intuition.
    intuition. }
    assert (Hreadflagsh1 : isPartitionFalse ptSh1ChildFromSh1 idxSh1 s ).
   { unfold isPartitionFalse.
    unfold consistency in *. 
    assert(Haccessva : accessibleVAIsNotPartitionDescriptor s) by intuition.
    unfold accessibleVAIsNotPartitionDescriptor in *.
    assert (Hflag : getPDFlag currentShadow1 shadow1 s = false).
    { apply Haccessva with currentPart currentPD phySh1Child.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      subst;assumption.
      apply nextEntryIsPPgetPd; intuition.
      apply nextEntryIsPPgetFstShadow;intuition.  
      repeat rewrite andb_true_iff in Hlegit.
      intuition.
      subst.
      apply isAccessibleMappedPage2 with (currentPartition s) ptSh1Child;intuition. }
    apply getPDFlagReadPDflag with currentShadow1 shadow1 currentPart;trivial.
    intuition.  
    apply Nat.eqb_neq.
    assert(Hfalsepge : (defaultPage =? ptSh1ChildFromSh1) = false) by trivial.
    apply beq_nat_false in Hfalsepge.
    unfold not;intros Hfalse'.
    rewrite Hfalse' in Hfalsepge.    
    now contradict Hfalsepge.
    intuition.
    intuition.
    intuition. }
   assert (Hreadflagsh2 : isPartitionFalse childSh2 idxSh2 s ).
   { unfold isPartitionFalse.
    unfold consistency in *. 
    assert(Haccessva : accessibleVAIsNotPartitionDescriptor s) by intuition.
    unfold accessibleVAIsNotPartitionDescriptor in *.
    assert (Hflag : getPDFlag currentShadow1 shadow2 s = false).
    { apply Haccessva with currentPart currentPD phySh2Child.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      subst;assumption.
      apply nextEntryIsPPgetPd; intuition.
      apply nextEntryIsPPgetFstShadow;intuition.  
      repeat rewrite andb_true_iff in Hlegit.
      intuition.
      subst.
      apply isAccessibleMappedPage2 with (currentPartition s) ptSh2Child;intuition. }
    apply getPDFlagReadPDflag with currentShadow1 shadow2 currentPart;trivial.
    intuition.  
    apply Nat.eqb_neq.
    assert(Hfalsepge : (defaultPage =? childSh2) = false) by trivial.
    apply beq_nat_false in Hfalsepge.
    unfold not;intros Hfalse'.
    rewrite Hfalse' in Hfalsepge.    
    now contradict Hfalsepge.
    intuition.
    intuition.
    intuition. }
   assert (Hreadflaglist : isPartitionFalse childListSh1 idxConfigPagesList s ).
   { unfold isPartitionFalse.
    unfold consistency in *. 
    assert(Haccessva : accessibleVAIsNotPartitionDescriptor s) by intuition.
    unfold accessibleVAIsNotPartitionDescriptor in *.
    assert (Hflag : getPDFlag currentShadow1 list s = false).
    { apply Haccessva with currentPart currentPD phyConfigPagesList.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      subst;assumption.
      apply nextEntryIsPPgetPd; intuition.
      apply nextEntryIsPPgetFstShadow;intuition.  
      repeat rewrite andb_true_iff in Hlegit.
      intuition.
      subst.
      apply isAccessibleMappedPage2 with (currentPartition s) ptConfigPagesList;intuition. }
    apply getPDFlagReadPDflag with currentShadow1 list currentPart;trivial.
    intuition.  
    apply Nat.eqb_neq.
    assert(Hfalsepge : (defaultPage =? childListSh1) = false) by trivial.
    apply beq_nat_false in Hfalsepge.
    unfold not;intros Hfalse'.
    rewrite Hfalse' in Hfalsepge.    
    now contradict Hfalsepge.
    intuition.
    intuition.
    intuition. }
    assert (Hreadflagdesc : isPartitionFalse ptRefChildFromSh1 idxRefChild s ).
   { unfold isPartitionFalse.
    unfold consistency in *. 
    assert(Haccessva : accessibleVAIsNotPartitionDescriptor s) by intuition.
    unfold accessibleVAIsNotPartitionDescriptor in *.
    assert (Hflag : getPDFlag currentShadow1 descChild s = false).
    { apply Haccessva with currentPart currentPD phyDescChild.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      subst;assumption.
      apply nextEntryIsPPgetPd; intuition.
      apply nextEntryIsPPgetFstShadow;intuition.  
      repeat rewrite andb_true_iff in Hlegit.
      intuition.
      subst.
      apply isAccessibleMappedPage2 with (currentPartition s) ptRefChild;intuition. }
    apply getPDFlagReadPDflag with currentShadow1 descChild currentPart;trivial.
    intuition.  
    apply Nat.eqb_neq.
    assert(Hfalsepge : (defaultPage =? ptRefChildFromSh1) = false) by trivial.
    apply beq_nat_false in Hfalsepge.
    unfold not;intros Hfalse'.
    rewrite Hfalse' in Hfalsepge.    
    now contradict Hfalsepge.
    intuition.
    intuition.
    intuition. }
    assert(HpdChildaccess : getAccessibleMappedPage currentPD s pdChild = Some phyPDChild).
    { intuition.
      assert(Heqentry : pa entry =phyPDChild).
      apply isEntryPageLookupEq with ptPDChild idxPDChild s;subst;trivial.
      rewrite <- Heqentry in *.
      apply isAccessibleMappedPage with ptPDChild;subst;trivial.
      repeat rewrite andb_true_iff in Hlegit.
      intuition. subst;trivial.
      repeat rewrite andb_true_iff in Hlegit.
      intuition. 
      subst;trivial. }
    assert(Hcurparts : In currentPart (getPartitions multiplexer s)).
    { unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      subst.
      assumption. }
    assert(Hcurpd : StateLib.getPd currentPart (memory s) = Some currentPD).
    { intuition. subst.
      apply nextEntryIsPPgetPd;trivial. }
    assert (Hpde : partitionDescriptorEntry s).
    { unfold consistency in *. intuition. }
    unfold partitionDescriptorEntry in *.
    generalize (Hpde currentPart Hcurparts PPRidx); clear Hpde; intros Hpde.
    
    assert(Hcurentparent : (exists entry : page, nextEntryIsPP currentPart PPRidx entry s /\
     entry <> defaultPage) ).
    { apply Hpde.
      do 4 right;left;trivial. }
    clear Hpde.
    assert (Hpde : partitionDescriptorEntry s).
    { unfold consistency in *. intuition. }
    unfold partitionDescriptorEntry in *.
    generalize (Hpde currentPart Hcurparts sh2idx); clear Hpde; intros Hpde.
    
    assert(Hcurrentsh2 : (exists entry : page, nextEntryIsPP currentPart sh2idx entry s /\
     entry <> defaultPage) ).
    { apply Hpde.
      do 2 right;left;trivial. }
    clear Hpde.
    assert(Hisaccessible : isAccessibleMappedPageInParent currentPart pdChild phyPDChild s = true).
               { assert(Hcons : consistency s).
        { unfold propagatedProperties in *.
          intuition. }
        unfold consistency in Hcons.
        assert(Haccess : accessibleChildPhysicalPageIsAccessibleIntoParent s) by intuition.
        unfold accessibleChildPhysicalPageIsAccessibleIntoParent in Haccess.
        apply Haccess with currentPD;intuition. }
    destruct H0 as (H0 & Hnew).
    try repeat rewrite and_assoc in H0.
    do 31 rewrite <- and_assoc in H0.
    destruct H0 as (H0 & Hsplit).
    subst. 
    destruct H0 as (H0 & Hfalse). 
    try repeat rewrite and_assoc in H0.
    assert (Hpost := conj (conj H0 Hsplit)  Hnew).

    assert(Hnewprops := conj (conj ( conj (conj (conj (conj Hphy  Hreadflagsh1) Hreadflagsh2) 
    Hreadflaglist)Hreadflagdesc ) Hreadflag) Hisaccessible).
        try repeat rewrite and_assoc in Hnewprops.
    assert (Hnewpost := conj Hpost Hnewprops).    
    pattern s in Hnewpost.
    match type of Hnewpost with 
    | ?HT s => instantiate (1 := fun tt s => HT s /\ 
                entryUserFlag ptPDChild idxPDChild false s )
    end.
    simpl.
    set (s' := {|
    currentPartition := currentPartition s;
    memory := add ptPDChild idxPDChild
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
    do 6 apply and_assoc.
    split.
  (** partitionsIsolation **) 
    assert (partitionsIsolation s ) as Hiso. intuition.
    clear Hpost Hsplit H0.
    unfold partitionsIsolation in *.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartitions. clear Hpartitions.
    intros.
    generalize (Hiso parent child1 child2); clear Hiso; intros Hiso. 
    assert(getChildren parent s' = getChildren parent s) as Hchildren.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite Hchildren in H2, H1. clear Hchildren.
    assert (getUsedPages child1 s'= getUsedPages child1 s) as Hch1used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch1used. clear Hch1used.
    assert (getUsedPages child2 s' = getUsedPages child2 s) as Hch2used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch2used. clear Hch2used.
    apply Hiso; trivial.
    apply and_assoc.
    split.
  (** kernelDataIsolation **)
    assert (kernelDataIsolation s) as HAncesiso. intuition.
    unfold kernelDataIsolation in *.
    intros.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartitions in *.
    clear Hpartitions.
    assert(  (getConfigPages partition2 s') = (getConfigPages partition2 s)) as Hconfig.
    apply getConfigPagesUpdateUserFlag; trivial.
    rewrite Hconfig. clear Hconfig.
    assert (incl (getAccessibleMappedPages partition1 s') (getAccessibleMappedPages partition1 s)).
    apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
    unfold disjoint in *.
    intros.
    unfold incl in *.
    apply HAncesiso with partition1; trivial.
    apply H3; trivial.
    apply and_assoc.
    split.
  (** Vertical Sharing **)
    unfold verticalSharing in *.
    assert (Hvs : verticalSharing s)  by intuition.
    clear Hpost Hsplit H0.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartitions. clear Hpartitions.
    intros.
    generalize (Hvs parent child); clear Hvs; intros Hvs.
    assert (getUsedPages child s' = getUsedPages child s) as Husedpage.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite   Husedpage.
    assert ( getMappedPages parent s' = getMappedPages parent s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd parent (memory s') = StateLib.getPd parent (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd parent (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. apply Hvs;trivial.
    assert (getChildren parent s' = getChildren parent s) as Hchild.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite <- Hchild. assumption.
    apply and_assoc.
    split.
  (** Consistency **) 
    assert (Hcons : consistency s) by intuition. 
    clear Hpost Hsplit H0.     
    unfold consistency in *.
    split.
    (** partitionDescriptorEntry **)
    apply partitionDescriptorEntryUpdateUserFlag;trivial.
    intuition.
    (** dataStructurePdSh1Sh2asRoot **)
    destruct Hcons as (Hpe & Hpd & Hsh1 & Hsh2 & Hcurpartlist & 
    Hnodupmapped & Hnodupconfig & Hparent & Hsh1struct).
    repeat split; try  apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
    unfold currentPartitionInPartitionsList in *.
    simpl in *. subst. 
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartitions. assumption.
    (** noDupMappedPagesList **)
    unfold noDupMappedPagesList in *.
    intros partition HgetPartnewstate.
    assert ( getMappedPages partition s' = getMappedPages partition s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd partition (memory s') = StateLib.getPd partition (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd partition (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. 
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag;trivial.
    rewrite HgetPart in HgetPartnewstate.
    apply Hnodupmapped;assumption.
    apply getIndirectionsNoDupUpdateUserFlag; trivial.
    (** parentInPartitionList **)
    unfold parentInPartitionList in *.
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite HgetPart.
    intros partition HgetParts parent Hroot.
    generalize (Hparent partition HgetParts); clear Hparent; intros Hparent; trivial.
    apply  nextEntryIsPPUpdateUserFlag' in  Hroot.
    apply Hparent; trivial.
    (** accessibleVAIsNotPartitionDescriptor **)
    unfold s'. 
    subst.
    apply accessibleVAIsNotPartitionDescriptorUpdateUserFlag with level
    (currentPartition s) currentPD ;trivial.
    assert(Hget : forall idx : index,
      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
      isPE ptPDChild idx s /\ 
      getTableAddrRoot ptPDChild PDidx (currentPartition s) pdChild s) by trivial.     
    assert(isPE ptPDChild (StateLib.getIndexOfAddr pdChild fstLevel) s /\ 
            getTableAddrRoot ptPDChild PDidx (currentPartition s) pdChild s)
    as (_ & Hi).
    apply Hget; trivial.
    assumption.
    apply isAccessibleMappedPage with ptPDChild;trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    (** accessibleChildPhysicalPageIsAccessibleIntoParent *)
    subst.
    assert(Htrue : accessibleChildPhysicalPageIsAccessibleIntoParent s) by intuition.
    unfold s'.
    assert(exists va : vaddr,
        isEntryVA ptPDChildSh1 (StateLib.getIndexOfAddr pdChild fstLevel) va s /\
        beqVAddr defaultVAddr va = derivedPDChild) as 
        (vaInAncestor & HvaInAncestor & Hnotderived) by trivial.
    destruct Hcurentparent as (ancestor & Hancestor & Hancestornotnull).
    assert(Hancestorpart : In ancestor (getPartitions multiplexer s)).
    unfold parentInPartitionList in *.
    apply Hparent with (currentPartition s);trivial.
    assert(Hpde : partitionDescriptorEntry s) by trivial.
    unfold partitionDescriptorEntry in *.
    assert(exists entry : page, nextEntryIsPP ancestor PDidx entry s /\ entry <> defaultPage) as (pdAncestor & Hpdancestor & Hpdancesnotnull).
    apply Hpde;trivial.
    left;trivial.      
    apply accessibleChildPhysicalPageIsAccessibleIntoParentUpdate with 
     (currentPartition s) currentPD level;
    trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition;subst;trivial.
    clear Hpost.
    rename H into Hcond. 
    assert (H := conj (conj (conj H0 Hfalse) Hsplit)  Hnew).
    clear H0 Hfalse Hsplit Hnew.
(** Propagated properties **)
    {  intuition try eassumption.     
      * apply nextEntryIsPPUpdateUserFlag ; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP);  intros (Htableroot & _). 
        apply isPEUpdateUserFlag; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP); intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * unfold s'.
        assert(ptRefChild <> ptPDChild \/ idxRefChild  <>idxPDChild).
        apply toApplyPageTablesOrIndicesAreDifferent with descChild pdChild currentPart
         currentPD PDidx level isPE s; trivial.
         left;trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * assert(Hi3 : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi3 idx HP);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;  assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP); intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption. 
     
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
         generalize (Hi idx Hi1); intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert(ptSh1Child  <> ptPDChild \/ idxSh1  <>idxPDChild).      
        apply toApplyPageTablesOrIndicesAreDifferent with  shadow1 pdChild currentPart
        currentPD PDidx level isPE s; trivial.
         left;trivial. 
        rewrite checkVAddrsEqualityWOOffsetPermut; trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi1 idx Hi2);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
         generalize (Hi1 idx Hi2); intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert( ptSh2Child <> ptPDChild \/ idxSh2 <> idxPDChild).
        apply toApplyPageTablesOrIndicesAreDifferent with shadow2
        pdChild   currentPart
        currentPD PDidx level isPE s; trivial.
         left;trivial. 
        rewrite checkVAddrsEqualityWOOffsetPermut; trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert(ptConfigPagesList <> ptPDChild \/ idxConfigPagesList <> idxPDChild ).
        apply toApplyPageTablesOrIndicesAreDifferent with list
        pdChild   currentPart
        currentPD PDidx level isPE s; trivial.
         left;trivial. 
        rewrite checkVAddrsEqualityWOOffsetPermut; trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * apply nextEntryIsPPUpdateUserFlag;assumption.  
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1); clear H7; intros (H7 & H7').      
        apply isVEUpdateUserFlag; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind. 
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                      isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChild)
                      by intuition.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                    isEntryVA ptPDChildSh1 idxPDChild va s /\ 
                    beqVAddr defaultVAddr va = derivedPDChild) by trivial. 
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
        isEntryVA ptSh1ChildFromSh1 idxSh1 va s /\ beqVAddr defaultVAddr va = derivedSh1Child) 
        by trivial.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr, isEntryVA childSh2 idxSh2 va s /\ 
                    beqVAddr defaultVAddr va = derivedSh2Child) by trivial.
      destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial. 
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert( Hi5 : exists va : vaddr,
                      isEntryVA childListSh1 idxConfigPagesList va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChildListSh1) by trivial.
        destruct Hi5 as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyPDChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phySh1Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phySh2Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyConfigPagesList (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial. 
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyDescChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      *  unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      *  unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      *  unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      *  unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      *  unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.      
      * assert(HisAccess : isAccessibleMappedPageInParent currentPart pdChild phyPDChild s' =
          isAccessibleMappedPageInParent currentPart pdChild phyPDChild s).
          { unfold isAccessibleMappedPageInParent.
            unfold s'.
            simpl.
            rewrite getSndShadowUpdateUserFlag;trivial.
            case_eq( StateLib.getSndShadow currentPart (memory s));
            intros * Hsh2 ;trivial.
            assert( Hvirt :  getVirtualAddressSh2 p
    {|
    currentPartition := currentPartition s;
    memory := add ptPDChild idxPDChild
                (PE
                   {|
                   read := read entry;
                   write := write entry;
                   exec := exec entry;
                   present := present entry;
                   user := false;
                   pa := pa entry |}) (memory s) beqPage beqIndex |} pdChild
                    =
                            getVirtualAddressSh2 p s pdChild).
            { unfold getVirtualAddressSh2.
              assert(HnbL: Some level = StateLib.getNbLevel) by trivial.
              rewrite <- HnbL;trivial.
              rewrite getIndirectionUpdateUserFlag;trivial.
              destruct(getIndirection p pdChild level (nbLevel - 1) s );trivial.
              simpl.
              rewrite readVirtualUpdateUserFlag;trivial. }
              rewrite Hvirt;trivial.
              case_eq (getVirtualAddressSh2 p s pdChild);
              intros * Hvainances;trivial.
              rewrite getParentUpdateUserFlag;trivial.
              case_eq( StateLib.getParent currentPart (memory s)); 
              intros * HparentAcestor;trivial.
              rewrite getPdUpdateUserFlag.
              case_eq(StateLib.getPd p0 (memory s) );
              intros * Hpdparentances;trivial.
              assert( Haccessible : 
                        getAccessibleMappedPage p1
    {|
    currentPartition := currentPartition s;
    memory := add ptPDChild idxPDChild
                (PE
                   {|
                   read := read entry;
                   write := write entry;
                   exec := exec entry;
                   present := present entry;
                   user := false;
                   pa := pa entry |}) (memory s) beqPage beqIndex |} v= 
                        getAccessibleMappedPage p1 s v).
              { symmetry.
                
                unfold consistency in *.
                assert (Hparentpart : parentInPartitionList s ) by  intuition.
                unfold parentInPartitionList in *.
                assert(Hancestor : In p0 (getPartitions multiplexer s)).
                apply Hparentpart with currentPart;trivial.
                apply nextEntryIsPPgetParent; trivial.
                subst.
                apply getAccessibleMappedPageUpdateUserFlagDiffrentPartitions 
                with (currentPartition s) p0;trivial.
                intuition.
                assert(Hget : forall idx : index,
                        StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                        isPE ptPDChild idx s /\ 
                        getTableAddrRoot ptPDChild PDidx (currentPartition s) pdChild s) by trivial.
                destruct Hget with (StateLib.getIndexOfAddr pdChild fstLevel)
                as (Hpe & Hroot);
                trivial.

                admit. (**p0 <> currentPartition s : parent and child partition descriptors are different **)
                admit. (* disjoint (getConfigPages (currentPartition s) s) (getConfigPages p0 s)  between 
                          current partition and current partition's parent *) }
              assert(Haccess : accessibleChildPhysicalPageIsAccessibleIntoParent s).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold accessibleChildPhysicalPageIsAccessibleIntoParent in *.
              assert(Hpde : partitionDescriptorEntry s ).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }

              rewrite Haccessible;trivial.
              assumption. }
          rewrite HisAccess.
          assumption.
      * (** New property **) 
        unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptPDChild, idxPDChild) (ptPDChild, idxPDChild)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity.  }
    intros [].
(** writeAccessibleRec : pdChild **)
    eapply bindRev.
    eapply weaken.
    eapply WriteAccessibleRec.
    simpl.
    intros.
    split. 
    destruct H0 as ((((H0 & Ha1 ) & Ha2) & Ha3) &Ha4).
    repeat rewrite <- and_assoc in Ha3.
    destruct Ha3 as (Ha3 & Hfalse).
    repeat rewrite and_assoc in Ha3.    
    assert(Hnew :=  conj ( conj ( conj ( conj H0 Ha4 ) Ha1 ) Ha2 ) Ha3).
    repeat rewrite and_assoc in Hnew.
    unfold propagatedProperties.
    eapply Hnew.
    instantiate(1:= phyPDChild).
    instantiate(1:= idxPDChild).
    instantiate(1:= ptPDChild).
    intuition.
    subst.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in*.
    intuition.
    subst.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    intros.    
(** writeAccessible : shadow1 **)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply WP.writeAccessible.
    intros. simpl.
    assert (exists entry : Pentry,
      lookup ptSh1Child idxSh1 (memory s) beqPage beqIndex = Some (PE entry)) as Hlookup.
    { apply isPELookupEq.
      unfold propagatedProperties in *.
      assert (forall idx : index,
       StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
       isPE ptSh1Child idx s /\ getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) as H1 by intuition.
      generalize (H1  idxSh1);clear H1; intros H1.
      assert (StateLib.getIndexOfAddr shadow1 fstLevel = idxSh1 ) as H2 by intuition.
      apply H1 in H2. intuition. }
    destruct Hlookup as (entry & Hlookup).
    unfold propagatedProperties in *.
    exists entry ; split;trivial.
(** Here the first shadow is still accessible, so we summarize this property  **)
    assert(HpdChildaccess : getAccessibleMappedPage currentPD s shadow1 = Some phySh1Child).
    { intuition.
      assert(Heqentry : pa entry =phySh1Child).
      apply isEntryPageLookupEq with ptSh1Child idxSh1 s;subst;trivial.
      rewrite <- Heqentry in *.
      apply isAccessibleMappedPage with ptSh1Child;subst;trivial.
      repeat rewrite andb_true_iff in Hlegit.
      intuition. subst;trivial.
      repeat rewrite andb_true_iff in Hlegit.
      intuition. 
      subst;trivial. }
    assert(Hcurparts : In currentPart (getPartitions multiplexer s)).
    { unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      subst.
      assumption. }
    assert(Hcurpd : StateLib.getPd currentPart (memory s) = Some currentPD).
    { intuition. subst.
      apply nextEntryIsPPgetPd;trivial. }
    assert (Hpde : partitionDescriptorEntry s).
    { unfold consistency in *. intuition. }
    unfold partitionDescriptorEntry in *.
    generalize (Hpde currentPart Hcurparts PPRidx); clear Hpde; intros Hpde.
    
    assert(Hcurentparent : (exists entry : page, nextEntryIsPP currentPart PPRidx entry s /\
     entry <> defaultPage) ).
    { apply Hpde.
      do 4 right;left;trivial. }
    clear Hpde.
    assert (Hpde : partitionDescriptorEntry s).
    { unfold consistency in *. intuition. }
    unfold partitionDescriptorEntry in *.
    generalize (Hpde currentPart Hcurparts sh2idx); clear Hpde; intros Hpde.
    
    assert(Hcurrentsh2 : (exists entry : page, nextEntryIsPP currentPart sh2idx entry s /\
     entry <> defaultPage) ).
    { apply Hpde.
      do 2 right;left;trivial. }
    clear Hpde.

(** Here the first shadow is still accessible, so we prove that in all ancestor this physical 
page is already accessible **)
     assert(Hisaccessible : isAccessibleMappedPageInParent currentPart shadow1 phySh1Child s = true).
           { assert(Hcons : consistency s).
        { unfold propagatedProperties in *.
          intuition. }
        unfold consistency in Hcons.
        assert(Haccess : accessibleChildPhysicalPageIsAccessibleIntoParent s) by intuition.
        unfold accessibleChildPhysicalPageIsAccessibleIntoParent in Haccess.
        apply Haccess with currentPD;intuition. }
    do 36 rewrite <- and_assoc in H0.
    destruct H0 as (Hi & Hsplit). 
    destruct Hi as (Hi & Hfalse). 
    try repeat rewrite and_assoc in Hi.
    assert (Hpost1 :=  conj  Hi Hsplit).
    assert (Hpost := conj Hpost1 Hisaccessible).
    pattern s in Hpost.
    match type of Hpost with 
    | ?HT s => instantiate (1 := fun tt s => HT s /\ 
                entryUserFlag ptSh1Child idxSh1 false s)
    end.
    simpl.
    set (s' := {|
    currentPartition := currentPartition s;
    memory := add ptSh1Child idxSh1
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
    do 8 rewrite and_assoc.             
    split. 
  (** partitionsIsolation **) 
    assert (partitionsIsolation s ) as Hiso. intuition.
    clear Hpost Hsplit.
    unfold partitionsIsolation in *.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartitions. clear Hpartitions.
    intros.
    generalize (Hiso parent child1 child2); clear Hiso; intros Hiso. 
    assert(getChildren parent s' = getChildren parent s) as Hchildren.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite Hchildren in H2, H1. clear Hchildren.
    assert (getUsedPages child1 s'= getUsedPages child1 s) as Hch1used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch1used. clear Hch1used.
    assert (getUsedPages child2 s' = getUsedPages child2 s) as Hch2used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch2used. clear Hch2used.
    apply Hiso; trivial.
    split.
  (** kernelDataIsolation **)
    assert (kernelDataIsolation s) as HAncesiso. intuition.
    unfold kernelDataIsolation in *.
    intros.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartitions in *.
    clear Hpartitions.
    assert(  (getConfigPages partition2 s') = (getConfigPages partition2 s)) as Hconfig.
    apply getConfigPagesUpdateUserFlag; trivial.
    rewrite Hconfig. clear Hconfig.
    assert (incl (getAccessibleMappedPages partition1 s') (getAccessibleMappedPages partition1 s)).
    apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
    unfold disjoint in *.
    intros.
    unfold incl in *.
    apply HAncesiso with partition1; trivial.
    apply H2; trivial.
(** Vertical Sharing **)
    split. unfold verticalSharing in *.
    assert (Hvs : verticalSharing s)  by intuition.
    clear Hpost Hsplit.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartitions. clear Hpartitions.
    intros.
    generalize (Hvs parent child); clear Hvs; intros Hvs.
    assert (getUsedPages child s' = getUsedPages child s) as Husedpage.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite   Husedpage.
    assert ( getMappedPages parent s' = getMappedPages parent s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd parent (memory s') = StateLib.getPd parent (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd parent (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. apply Hvs;trivial.
    assert (getChildren parent s' = getChildren parent s) as Hchild.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite <- Hchild. assumption.
    split.
  (** Consistency **) 
    assert (Hcons : consistency s) by intuition. 
    clear Hsplit.     
    unfold consistency in *.
    split. apply partitionDescriptorEntryUpdateUserFlag;trivial.
    intuition.
    destruct Hcons as (Hpe & Hpd & Hsh1 & Hsh2 & Hcurpartlist & 
    Hnodupmapped & Hnodupconfig & Hparent & Hsh1struct).
    clear Hpost1 Hi.
    repeat split; try  apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
    unfold currentPartitionInPartitionsList in *.
    simpl in *. subst. 
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartitions. assumption.
    unfold noDupMappedPagesList in *.
    intros partition HgetPartnewstate.
    assert ( getMappedPages partition s' = getMappedPages partition s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd partition (memory s') = StateLib.getPd partition (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd partition (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. 
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag;trivial.
    rewrite HgetPart in HgetPartnewstate.
    apply Hnodupmapped;assumption.
    apply getIndirectionsNoDupUpdateUserFlag; trivial.
    unfold parentInPartitionList in *.
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite HgetPart.
    intros partition HgetParts parent Hroot.
    generalize (Hparent partition HgetParts); clear Hparent; intros Hparent; trivial.
    apply  nextEntryIsPPUpdateUserFlag' in  Hroot.
    apply Hparent; trivial.
    (** accessibleVAIsNotPartitionDescriptor **)
    unfold s'. 
    subst.
    apply accessibleVAIsNotPartitionDescriptorUpdateUserFlag with level
    (currentPartition s) currentPD ;trivial.
    assert(Hget : forall idx : index,
      StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
      isPE ptSh1Child idx s /\ 
      getTableAddrRoot ptSh1Child PDidx (currentPartition s) shadow1 s) by trivial.     
    assert(isPE ptSh1Child (StateLib.getIndexOfAddr shadow1 fstLevel) s /\ 
            getTableAddrRoot ptSh1Child PDidx (currentPartition s) shadow1 s)
    as (_ & Hi).
    apply Hget; trivial.
    assumption.
    apply isAccessibleMappedPage with ptSh1Child;trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    (** accessibleChildPhysicalPageIsAccessibleIntoParent *)
    subst.
    assert(Htrue : accessibleChildPhysicalPageIsAccessibleIntoParent s) by intuition.
    unfold s'.
     assert(exists va : vaddr,
        isEntryVA ptSh1ChildFromSh1 (StateLib.getIndexOfAddr shadow1 fstLevel) va s /\
        beqVAddr defaultVAddr va = derivedSh1Child) as 
        (vaInAncestor & HvaInAncestor & Hnotderived) by trivial.
   destruct Hcurentparent as (ancestor & Hancestor & Hancestornotnull).
   assert(Hancestorpart : In ancestor (getPartitions multiplexer s)).
   unfold parentInPartitionList in *.
   apply Hparent with (currentPartition s);trivial.
   assert(Hpde : partitionDescriptorEntry s) by trivial.
   unfold partitionDescriptorEntry in *.
   assert(exists entry : page, nextEntryIsPP ancestor PDidx entry s /\ entry <> defaultPage) as (pdAncestor & Hpdancestor & Hpdancesnotnull).
   apply Hpde;trivial.
   left;trivial.
      
    apply accessibleChildPhysicalPageIsAccessibleIntoParentUpdate with  (currentPartition s) currentPD level;
    trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition;subst;trivial.
    clear Hpost.
    rename H into Hcond. 
    assert (H :=  (conj (conj Hpost1 Hfalse) Hsplit)  ).
    clear Hpost1 Hfalse Hsplit .
(** Propagated properties **)
    {
      intuition try trivial. 
      * apply nextEntryIsPPUpdateUserFlag ; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP); clear H23; intros (H23 & _). 
        apply isPEUpdateUserFlag; assumption.
      *  assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * unfold s'.
        assert(ptRefChild <> ptSh1Child \/ idxRefChild  <>idxSh1).
        apply toApplyPageTablesOrIndicesAreDifferent with descChild shadow1 currentPart
          currentPD PDidx level isPE s; trivial.
         left;trivial.  
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * assert(Hi3 : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi3 idx HP);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;  assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * apply entryUserFlagUpdateUserFlagSameValue; trivial.
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi1 idx Hi2);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi1 idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * unfold s'. assert( ptSh2Child <> ptSh1Child \/ idxSh2 <> idxSh1).
        apply toApplyPageTablesOrIndicesAreDifferent with shadow2
        shadow1   currentPart
        currentPD PDidx level isPE s; trivial.
         left;trivial. 
        rewrite checkVAddrsEqualityWOOffsetPermut; trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert(ptConfigPagesList <> ptSh1Child \/ idxConfigPagesList <> idxSh1 ).
        apply toApplyPageTablesOrIndicesAreDifferent with list
        shadow1   currentPart
        currentPD PDidx level isPE s; trivial.
         left;trivial. 
        rewrite checkVAddrsEqualityWOOffsetPermut; trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * apply nextEntryIsPPUpdateUserFlag;assumption.  
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1); clear H7; intros (H7 & H7').      
        apply isVEUpdateUserFlag; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                      isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChild)
                      by intuition.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                    isEntryVA ptPDChildSh1 idxPDChild va s /\ 
                    beqVAddr defaultVAddr va = derivedPDChild) by trivial. 
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
        isEntryVA ptSh1ChildFromSh1 idxSh1 va s /\ beqVAddr defaultVAddr va = derivedSh1Child) 
        by trivial.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr, isEntryVA childSh2 idxSh2 va s /\ 
                    beqVAddr defaultVAddr va = derivedSh2Child) by trivial.
      destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial. 
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert( Hi5 : exists va : vaddr,
                      isEntryVA childListSh1 idxConfigPagesList va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChildListSh1) by trivial.
        destruct Hi5 as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyPDChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phySh1Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phySh2Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyConfigPagesList (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial. 
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyDescChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial. 
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial. 
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.  
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.  
      * assert(HisAccess : isAccessibleMappedPageInParent currentPart shadow1 phySh1Child s' =
          isAccessibleMappedPageInParent currentPart shadow1 phySh1Child s).
          { unfold isAccessibleMappedPageInParent.
            unfold s'.
            simpl.
            rewrite getSndShadowUpdateUserFlag;trivial.
            case_eq( StateLib.getSndShadow currentPart (memory s));
            intros * Hsh2 ;trivial.
            assert( Hvirt :  getVirtualAddressSh2 p
    {|
    currentPartition := currentPartition s;
    memory := add ptSh1Child idxSh1
                (PE
                   {|
                   read := read entry;
                   write := write entry;
                   exec := exec entry;
                   present := present entry;
                   user := false;
                   pa := pa entry |}) (memory s) beqPage beqIndex |} shadow1
                    =
                            getVirtualAddressSh2 p s shadow1).
            { unfold getVirtualAddressSh2.
              assert(HnbL: Some level = StateLib.getNbLevel) by trivial.
              rewrite <- HnbL;trivial.
              rewrite getIndirectionUpdateUserFlag;trivial.
              destruct(getIndirection p shadow1 level (nbLevel - 1) s );trivial.
              simpl.
              rewrite readVirtualUpdateUserFlag;trivial. }
              rewrite Hvirt;trivial.
              case_eq (getVirtualAddressSh2 p s shadow1);
              intros * Hvainances;trivial.
              rewrite getParentUpdateUserFlag;trivial.
              case_eq( StateLib.getParent currentPart (memory s)); 
              intros * HparentAcestor;trivial.
              rewrite getPdUpdateUserFlag.
              case_eq(StateLib.getPd p0 (memory s) );
              intros * Hpdparentances;trivial.
              assert( Haccessible : 
                        getAccessibleMappedPage p1
    {|
    currentPartition := currentPartition s;
    memory := add ptSh1Child idxSh1
                (PE
                   {|
                   read := read entry;
                   write := write entry;
                   exec := exec entry;
                   present := present entry;
                   user := false;
                   pa := pa entry |}) (memory s) beqPage beqIndex |} v= 
                        getAccessibleMappedPage p1 s v).
              { symmetry.
                
                unfold consistency in *.
                assert (Hparentpart : parentInPartitionList s ) by  intuition.
                unfold parentInPartitionList in *.
                assert(Hancestor : In p0 (getPartitions multiplexer s)).
                apply Hparentpart with currentPart;trivial.
                apply nextEntryIsPPgetParent; trivial.
                subst.
                apply getAccessibleMappedPageUpdateUserFlagDiffrentPartitions 
                with (currentPartition s) p0;trivial.
                intuition.
                assert(Hget : forall idx : index,
                        StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                        isPE ptSh1Child idx s /\ 
                        getTableAddrRoot ptSh1Child PDidx (currentPartition s) shadow1 s) by trivial.
                destruct Hget with (StateLib.getIndexOfAddr shadow1 fstLevel)
                as (Hpe & Hroot);
                trivial.

                admit. (**p0 <> currentPartition s : parent and child partition descriptors are different **)
                admit. (* disjoint (getConfigPages (currentPartition s) s) (getConfigPages p0 s)  between 
                          current partition and current partition's parent *) }
              assert(Haccess : accessibleChildPhysicalPageIsAccessibleIntoParent s).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold accessibleChildPhysicalPageIsAccessibleIntoParent in *.
              assert(Hpde : partitionDescriptorEntry s ).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }

              rewrite Haccessible;trivial.
              assumption. }
          rewrite HisAccess.
          assumption.
(** New property **) 
      * unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptSh1Child, idxSh1) (ptSh1Child, idxSh1) beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity. } 
    intros [].
(** writeAccessibleRec : shadow 1 **)
    eapply bindRev.
    eapply weaken.
    eapply WriteAccessibleRec.
    
    simpl.
    intros.
    split. 
    instantiate (42 := false).
        destruct H0 as (((H0  & Huserpd) &Haccesssh1) & Husersh1).
    assert(H0new := conj( conj H0 Husersh1) Huserpd ).
    
      repeat rewrite and_assoc in H0new.

    unfold propagatedProperties.
    eapply H0new.
    instantiate(1:= phySh1Child).
    instantiate(1:= idxSh1).
    instantiate(1:= ptSh1Child).
    intuition.
    subst.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in*.
    intuition.
    subst.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    intros.
(** writeAccessible : shadow 2 **)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply WP.writeAccessible.
    intros. simpl.
    assert (exists entry : Pentry,
      lookup ptSh2Child idxSh2 (memory s) beqPage beqIndex = Some (PE entry)) as Hlookup.
    { apply isPELookupEq.
      unfold propagatedProperties in *.
      assert (forall idx : index,
       StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
       isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) as H1 by intuition.
      generalize (H1  idxSh2);clear H1; intros H1.
      assert (StateLib.getIndexOfAddr shadow2 fstLevel = idxSh2 ) as H2 by intuition.
      apply H1 in H2. intuition. }
    destruct Hlookup as (entry & Hlookup).
    unfold propagatedProperties in *.
    exists entry ; split;trivial.
(** Here the first shadow is still accessible, so we summarize this property  **)
    assert(HpdChildaccess : getAccessibleMappedPage currentPD s shadow2 = Some phySh2Child).
    { intuition.
      assert(Heqentry : pa entry =phySh2Child).
      apply isEntryPageLookupEq with ptSh2Child idxSh2 s;subst;trivial.
      rewrite <- Heqentry in *.
      apply isAccessibleMappedPage with ptSh2Child;subst;trivial.
      repeat rewrite andb_true_iff in Hlegit.
      intuition. subst;trivial.
      repeat rewrite andb_true_iff in Hlegit.
      intuition. 
      subst;trivial. }
    assert(Hcurparts : In currentPart (getPartitions multiplexer s)).
    { unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      subst.
      assumption. }
    assert(Hcurpd : StateLib.getPd currentPart (memory s) = Some currentPD).
    { intuition. subst.
      apply nextEntryIsPPgetPd;trivial. }
    assert (Hpde : partitionDescriptorEntry s).
    { unfold consistency in *. intuition. }
    unfold partitionDescriptorEntry in *.
    generalize (Hpde currentPart Hcurparts PPRidx); clear Hpde; intros Hpde.
    
    assert(Hcurentparent : (exists entry : page, nextEntryIsPP currentPart PPRidx entry s /\
     entry <> defaultPage) ).
    { apply Hpde.
      do 4 right;left;trivial. }
    clear Hpde.
    assert (Hpde : partitionDescriptorEntry s).
    { unfold consistency in *. intuition. }
    unfold partitionDescriptorEntry in *.
    generalize (Hpde currentPart Hcurparts sh2idx); clear Hpde; intros Hpde.
    
    assert(Hcurrentsh2 : (exists entry : page, nextEntryIsPP currentPart sh2idx entry s /\
     entry <> defaultPage) ).
    { apply Hpde.
      do 2 right;left;trivial. }
    clear Hpde.

(** Here the first shadow is still accessible, so we prove that in all ancestor this physical 
page is already accessible **)
     assert(Hisaccessible : isAccessibleMappedPageInParent currentPart shadow2 phySh2Child s = true).
           { assert(Hcons : consistency s).
        { unfold propagatedProperties in *.
          intuition. }
        unfold consistency in Hcons.
        assert(Haccess : accessibleChildPhysicalPageIsAccessibleIntoParent s) by intuition.
        unfold accessibleChildPhysicalPageIsAccessibleIntoParent in Haccess.
        apply Haccess with currentPD;intuition. }
    
      do 41 rewrite <- and_assoc in H0.

    destruct H0 as (Hi & Hsplit). 
    destruct Hi as (Hi & Hfalse). 
    try repeat rewrite and_assoc in Hi.
    assert (Hpost1 := conj  Hi Hsplit) .
    assert (Hpost := conj Hpost1  Hisaccessible).
    pattern s in Hpost.
    match type of Hpost with 
    | ?HT s => instantiate (1 := fun tt s => HT s /\ 
                entryUserFlag ptSh2Child idxSh2 false s)
    end.
    simpl.
    set (s' := {|
    currentPartition := currentPartition s;
    memory := add ptSh2Child idxSh2
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
    do 8 rewrite and_assoc.             
    split. 
  (** partitionsIsolation **) 
    assert (partitionsIsolation s ) as Hiso. intuition.
    clear Hpost Hsplit.
    unfold partitionsIsolation in *.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartitions. clear Hpartitions.
    intros.
    generalize (Hiso parent child1 child2); clear Hiso; intros Hiso. 
    assert(getChildren parent s' = getChildren parent s) as Hchildren.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite Hchildren in H2, H1. clear Hchildren.
    assert (getUsedPages child1 s'= getUsedPages child1 s) as Hch1used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch1used. clear Hch1used.
    assert (getUsedPages child2 s' = getUsedPages child2 s) as Hch2used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch2used. clear Hch2used.
    apply Hiso; trivial.
    split.
  (** kernelDataIsolation **)
    assert (kernelDataIsolation s) as HAncesiso. intuition.
    unfold kernelDataIsolation in *.
    intros.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartitions in *.
    clear Hpartitions.
    assert(  (getConfigPages partition2 s') = (getConfigPages partition2 s)) as Hconfig.
    apply getConfigPagesUpdateUserFlag; trivial.
    rewrite Hconfig. clear Hconfig.
    assert (incl (getAccessibleMappedPages partition1 s') (getAccessibleMappedPages partition1 s)).
    apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
    unfold disjoint in *.
    intros.
    unfold incl in *.
    apply HAncesiso with partition1; trivial.
    apply H2; trivial.
(** Vertical Sharing **)
    split. unfold verticalSharing in *.
    assert (Hvs : verticalSharing s)  by intuition.
    clear Hpost Hsplit.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartitions. clear Hpartitions.
    intros.
    generalize (Hvs parent child); clear Hvs; intros Hvs.
    assert (getUsedPages child s' = getUsedPages child s) as Husedpage.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite   Husedpage.
    assert ( getMappedPages parent s' = getMappedPages parent s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd parent (memory s') = StateLib.getPd parent (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd parent (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. apply Hvs;trivial.
    assert (getChildren parent s' = getChildren parent s) as Hchild.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite <- Hchild. assumption.
    split.
  (** Consistency **) 
    assert (Hcons : consistency s) by intuition. 
    clear Hsplit.     
    unfold consistency in *.
    split. apply partitionDescriptorEntryUpdateUserFlag;trivial.
    intuition.
    destruct Hcons as (Hpe & Hpd & Hsh1 & Hsh2 & Hcurpartlist & 
    Hnodupmapped & Hnodupconfig & Hparent & Hsh1struct).
    clear Hpost1 Hi.
    repeat split; try  apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
    unfold currentPartitionInPartitionsList in *.
    simpl in *. subst. 
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartitions. assumption.
    unfold noDupMappedPagesList in *.
    intros partition HgetPartnewstate.
    assert ( getMappedPages partition s' = getMappedPages partition s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd partition (memory s') = StateLib.getPd partition (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd partition (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. 
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag;trivial.
    rewrite HgetPart in HgetPartnewstate.
    apply Hnodupmapped;assumption.
    apply getIndirectionsNoDupUpdateUserFlag; trivial.
    unfold parentInPartitionList in *.
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite HgetPart.
    intros partition HgetParts parent Hroot.
    generalize (Hparent partition HgetParts); clear Hparent; intros Hparent; trivial.
    apply  nextEntryIsPPUpdateUserFlag' in  Hroot.
    apply Hparent; trivial.
    (** accessibleVAIsNotPartitionDescriptor **)
    unfold s'. 
    subst.
    apply accessibleVAIsNotPartitionDescriptorUpdateUserFlag with level
    (currentPartition s) currentPD ;trivial.
    assert(Hget : forall idx : index,
      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
      isPE ptSh2Child idx s /\ 
      getTableAddrRoot ptSh2Child PDidx (currentPartition s) shadow2 s) by trivial.     
    assert(isPE ptSh2Child (StateLib.getIndexOfAddr shadow2 fstLevel) s /\ 
            getTableAddrRoot ptSh2Child PDidx (currentPartition s) shadow2 s)
    as (_ & Hi).
    apply Hget; trivial.
    assumption.
    apply isAccessibleMappedPage with ptSh2Child;trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    (** accessibleChildPhysicalPageIsAccessibleIntoParent *)
    subst.
    assert(Htrue : accessibleChildPhysicalPageIsAccessibleIntoParent s) by intuition.
    unfold s'.
     assert(exists va : vaddr,
        isEntryVA childSh2 (StateLib.getIndexOfAddr shadow2 fstLevel) va s /\
        beqVAddr defaultVAddr va = derivedSh2Child) as 
        (vaInAncestor & HvaInAncestor & Hnotderived) by trivial.
   destruct Hcurentparent as (ancestor & Hancestor & Hancestornotnull).
   assert(Hancestorpart : In ancestor (getPartitions multiplexer s)).
   unfold parentInPartitionList in *.
   apply Hparent with (currentPartition s);trivial.
   assert(Hpde : partitionDescriptorEntry s) by trivial.
   unfold partitionDescriptorEntry in *.
   assert(exists entry : page, nextEntryIsPP ancestor PDidx entry s /\ entry <> defaultPage) as (pdAncestor & Hpdancestor & Hpdancesnotnull).
   apply Hpde;trivial.
   left;trivial.
      
    apply accessibleChildPhysicalPageIsAccessibleIntoParentUpdate with  
    (currentPartition s) currentPD level;
    trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition;subst;trivial.
    clear Hpost.
    rename H into Hcond. 
    assert (H :=  (conj (conj Hpost1 Hfalse) Hsplit) ).
    clear Hpost1 Hfalse Hsplit .
(** Propagated properties **)
    { intuition try eassumption. 
      * apply nextEntryIsPPUpdateUserFlag ; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP); clear H23; intros (H23 & _). 
        apply isPEUpdateUserFlag; assumption.
      *  assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * unfold s'.
        assert(ptRefChild <> ptSh2Child \/ idxRefChild  <>idxSh2).
        apply toApplyPageTablesOrIndicesAreDifferent with descChild shadow2 currentPart
         currentPD PDidx level isPE s; trivial.
         left;trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * assert(Hi3 : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi3 idx HP);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;  assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * apply entryUserFlagUpdateUserFlagSameValue;trivial.
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * apply entryUserFlagUpdateUserFlagSameValue; trivial.
      *  assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi1 idx Hi2);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi1 idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial.  
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert(ptConfigPagesList <> ptSh2Child \/ idxConfigPagesList <> idxSh2 ).
        apply toApplyPageTablesOrIndicesAreDifferent with list
        shadow2   currentPart
        currentPD PDidx level isPE s; trivial.
         left;trivial. 
        rewrite checkVAddrsEqualityWOOffsetPermut; trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * apply nextEntryIsPPUpdateUserFlag;assumption.  
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1); clear H7; intros (H7 & H7').      
        apply isVEUpdateUserFlag; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                      isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChild)
                      by intuition.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                    isEntryVA ptPDChildSh1 idxPDChild va s /\ 
                    beqVAddr defaultVAddr va = derivedPDChild) by trivial. 
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
        isEntryVA ptSh1ChildFromSh1 idxSh1 va s /\ beqVAddr defaultVAddr va = derivedSh1Child) 
        by trivial.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr, isEntryVA childSh2 idxSh2 va s /\ 
                    beqVAddr defaultVAddr va = derivedSh2Child) by trivial.
      destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial. 
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert( Hi5 : exists va : vaddr,
                      isEntryVA childListSh1 idxConfigPagesList va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChildListSh1) by trivial.
        destruct Hi5 as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyPDChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phySh1Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phySh2Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyConfigPagesList (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial. 
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyDescChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial. 
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      * assert(HisAccess : isAccessibleMappedPageInParent currentPart shadow2 phySh2Child s' =
          isAccessibleMappedPageInParent currentPart shadow2 phySh2Child s).
          { unfold isAccessibleMappedPageInParent.
            unfold s'.
            simpl.
            rewrite getSndShadowUpdateUserFlag;trivial.
            case_eq( StateLib.getSndShadow currentPart (memory s));
            intros * Hsh2 ;trivial.
            assert( Hvirt :  getVirtualAddressSh2 p
    {|
    currentPartition := currentPartition s;
    memory := add ptSh2Child idxSh2
                (PE
                   {|
                   read := read entry;
                   write := write entry;
                   exec := exec entry;
                   present := present entry;
                   user := false;
                   pa := pa entry |}) (memory s) beqPage beqIndex |} shadow2
                    =
                            getVirtualAddressSh2 p s shadow2).
            { unfold getVirtualAddressSh2.
              assert(HnbL: Some level = StateLib.getNbLevel) by trivial.
              rewrite <- HnbL;trivial.
              rewrite getIndirectionUpdateUserFlag;trivial.
              destruct(getIndirection p shadow2 level (nbLevel - 1) s );trivial.
              simpl.
              rewrite readVirtualUpdateUserFlag;trivial. }
              rewrite Hvirt;trivial.
              case_eq (getVirtualAddressSh2 p s shadow2);
              intros * Hvainances;trivial.
              rewrite getParentUpdateUserFlag;trivial.
              case_eq( StateLib.getParent currentPart (memory s)); 
              intros * HparentAcestor;trivial.
              rewrite getPdUpdateUserFlag.
              case_eq(StateLib.getPd p0 (memory s) );
              intros * Hpdparentances;trivial.
              assert( Haccessible : 
                        getAccessibleMappedPage p1
    {|
    currentPartition := currentPartition s;
    memory := add ptSh2Child idxSh2
                (PE
                   {|
                   read := read entry;
                   write := write entry;
                   exec := exec entry;
                   present := present entry;
                   user := false;
                   pa := pa entry |}) (memory s) beqPage beqIndex |} v= 
                        getAccessibleMappedPage p1 s v).
              { symmetry.
                
                unfold consistency in *.
                assert (Hparentpart : parentInPartitionList s ) by  intuition.
                unfold parentInPartitionList in *.
                assert(Hancestor : In p0 (getPartitions multiplexer s)).
                apply Hparentpart with currentPart;trivial.
                apply nextEntryIsPPgetParent; trivial.
                subst.
                apply getAccessibleMappedPageUpdateUserFlagDiffrentPartitions 
                with (currentPartition s) p0;trivial.
                intuition.
                assert(Hget : forall idx : index,
                        StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                        isPE ptSh2Child idx s /\ 
                        getTableAddrRoot ptSh2Child PDidx (currentPartition s) shadow2 s) by trivial.
                destruct Hget with (StateLib.getIndexOfAddr shadow2 fstLevel)
                as (Hpe & Hroot);
                trivial.

                admit. (**p0 <> currentPartition s : parent and child partition descriptors are different **)
                admit. (* disjoint (getConfigPages (currentPartition s) s) (getConfigPages p0 s)  between 
                          current partition and current partition's parent *) }
              assert(Haccess : accessibleChildPhysicalPageIsAccessibleIntoParent s).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold accessibleChildPhysicalPageIsAccessibleIntoParent in *.
              assert(Hpde : partitionDescriptorEntry s ).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }

              rewrite Haccessible;trivial.
              assumption. }
          rewrite HisAccess.
          assumption.
(** New property **) 
      * unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptSh2Child, idxSh2) (ptSh2Child, idxSh2) beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity. } 
    intros [].
(** writeAccessibleRec : shadow 2 **)
    eapply bindRev.
    eapply weaken.
    eapply WriteAccessibleRec.
    simpl.
    intros.
    split. 
    instantiate (42 := false).
    instantiate (41 := false).
        destruct H0 as (((H0  &Hc) 
        & Hd ) & He).

    assert(H0new := conj( conj H0  He )Hc ).    
      repeat rewrite and_assoc in H0new.

    unfold propagatedProperties.
    eapply H0new.
    instantiate(1:= phySh2Child).
    instantiate(1:= idxSh2).
    instantiate(1:= ptSh2Child).
    intuition.
    subst.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in*.
    intuition.
    subst.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    intros.
    simpl.
(** writeAccessible : list  **)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply WP.writeAccessible.
    intros. simpl.
        assert (exists entry : Pentry,
      lookup ptConfigPagesList idxConfigPagesList (memory s) beqPage beqIndex = Some (PE entry)) as Hlookup.
    { apply isPELookupEq.
      unfold propagatedProperties in *.
      assert (forall idx : index,
       StateLib.getIndexOfAddr list fstLevel = idx ->
       isPE ptConfigPagesList idx s /\ 
       getTableAddrRoot ptConfigPagesList PDidx currentPart list s) as H1 by intuition.
      generalize (H1  idxConfigPagesList);clear H1; intros H1.
      assert (StateLib.getIndexOfAddr list fstLevel = idxConfigPagesList ) as H2 by intuition.
      apply H1 in H2. intuition. }
    destruct Hlookup as (entry & Hlookup).
    unfold propagatedProperties in *.
    exists entry ; split;trivial.
(** Here the first shadow is still accessible, so we summarize this property  **)
    assert(HpdChildaccess : getAccessibleMappedPage currentPD s list = Some phyConfigPagesList).
    { intuition.
      assert(Heqentry : pa entry =phyConfigPagesList).
      apply isEntryPageLookupEq with ptConfigPagesList idxConfigPagesList s;subst;trivial.
      rewrite <- Heqentry in *.
      apply isAccessibleMappedPage with ptConfigPagesList;subst;trivial.
      repeat rewrite andb_true_iff in Hlegit.
      intuition. subst;trivial.
      repeat rewrite andb_true_iff in Hlegit.
      intuition. 
      subst;trivial. }
    assert(Hcurparts : In currentPart (getPartitions multiplexer s)).
    { unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      subst.
      assumption. }
    assert(Hcurpd : StateLib.getPd currentPart (memory s) = Some currentPD).
    { intuition. subst.
      apply nextEntryIsPPgetPd;trivial. }
    assert (Hpde : partitionDescriptorEntry s).
    { unfold consistency in *. intuition. }
    unfold partitionDescriptorEntry in *.
    generalize (Hpde currentPart Hcurparts PPRidx); clear Hpde; intros Hpde.
    
    assert(Hcurentparent : (exists entry : page, nextEntryIsPP currentPart PPRidx entry s /\
     entry <> defaultPage) ).
    { apply Hpde.
      do 4 right;left;trivial. }
    clear Hpde.
    assert (Hpde : partitionDescriptorEntry s).
    { unfold consistency in *. intuition. }
    unfold partitionDescriptorEntry in *.
    generalize (Hpde currentPart Hcurparts sh2idx); clear Hpde; intros Hpde.
    
    assert(Hcurrentsh2 : (exists entry : page, nextEntryIsPP currentPart sh2idx entry s /\
     entry <> defaultPage) ).
    { apply Hpde.
      do 2 right;left;trivial. }
    clear Hpde.

(** Here the first shadow is still accessible, so we prove that in all ancestor this physical 
page is already accessible **)
     assert(Hisaccessible : isAccessibleMappedPageInParent currentPart list phyConfigPagesList s = true).
           { assert(Hcons : consistency s).
        { unfold propagatedProperties in *.
          intuition. }
        unfold consistency in Hcons.
        assert(Haccess : accessibleChildPhysicalPageIsAccessibleIntoParent s) by intuition.
        unfold accessibleChildPhysicalPageIsAccessibleIntoParent in Haccess.
        apply Haccess with currentPD;intuition. }

    
      do 46 rewrite <- and_assoc in H0.
    destruct H0 as (Hi & Hsplit). 
    destruct Hi as (Hi & Hfalse). 
    try repeat rewrite and_assoc in Hi.
    assert (Hpost1 := conj  Hi Hsplit  ).

    assert (Hpost := conj Hpost1  Hisaccessible).
    pattern s in Hpost.
    match type of Hpost with 
    | ?HT s => instantiate (1 := fun tt s => HT s /\ 
                entryUserFlag ptConfigPagesList idxConfigPagesList false s)
    end.
    simpl.
    set (s' := {|
    currentPartition := currentPartition s;
    memory := add  ptConfigPagesList idxConfigPagesList
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
    do 8 rewrite and_assoc.             
    split. 
  (** partitionsIsolation **) 
    assert (partitionsIsolation s ) as Hiso. intuition.
    clear Hpost Hsplit.
    unfold partitionsIsolation in *.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartitions. clear Hpartitions.
    intros.
    generalize (Hiso parent child1 child2); clear Hiso; intros Hiso. 
    assert(getChildren parent s' = getChildren parent s) as Hchildren.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite Hchildren in H2, H1. clear Hchildren.
    assert (getUsedPages child1 s'= getUsedPages child1 s) as Hch1used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch1used. clear Hch1used.
    assert (getUsedPages child2 s' = getUsedPages child2 s) as Hch2used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch2used. clear Hch2used.
    apply Hiso; trivial.
    split.
  (** kernelDataIsolation **)
    assert (kernelDataIsolation s) as HAncesiso. intuition.
    unfold kernelDataIsolation in *.
    intros.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartitions in *.
    clear Hpartitions.
    assert(  (getConfigPages partition2 s') = (getConfigPages partition2 s)) as Hconfig.
    apply getConfigPagesUpdateUserFlag; trivial.
    rewrite Hconfig. clear Hconfig.
    assert (incl (getAccessibleMappedPages partition1 s') (getAccessibleMappedPages partition1 s)).
    apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
    unfold disjoint in *.
    intros.
    unfold incl in *.
    apply HAncesiso with partition1; trivial.
    apply H2; trivial.
(** Vertical Sharing **)
    split. unfold verticalSharing in *.
    assert (Hvs : verticalSharing s)  by intuition.
    clear Hpost Hsplit.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartitions. clear Hpartitions.
    intros.
    generalize (Hvs parent child); clear Hvs; intros Hvs.
    assert (getUsedPages child s' = getUsedPages child s) as Husedpage.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite   Husedpage.
    assert ( getMappedPages parent s' = getMappedPages parent s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd parent (memory s') = StateLib.getPd parent (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd parent (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. apply Hvs;trivial.
    assert (getChildren parent s' = getChildren parent s) as Hchild.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite <- Hchild. assumption.
    split.
  (** Consistency **) 
    assert (Hcons : consistency s) by intuition. 
    clear Hsplit.     
    unfold consistency in *.
    split. apply partitionDescriptorEntryUpdateUserFlag;trivial.
    intuition.
    destruct Hcons as (Hpe & Hpd & Hsh1 & Hsh2 & Hcurpartlist & 
    Hnodupmapped & Hnodupconfig & Hparent & Hsh1struct).
    clear Hpost1 Hi.
    repeat split; try  apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
    unfold currentPartitionInPartitionsList in *.
    simpl in *. subst. 
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartitions. assumption.
    unfold noDupMappedPagesList in *.
    intros partition HgetPartnewstate.
    assert ( getMappedPages partition s' = getMappedPages partition s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd partition (memory s') = StateLib.getPd partition (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd partition (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. 
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag;trivial.
    rewrite HgetPart in HgetPartnewstate.
    apply Hnodupmapped;assumption.
    apply getIndirectionsNoDupUpdateUserFlag; trivial.
    unfold parentInPartitionList in *.
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite HgetPart.
    intros partition HgetParts parent Hroot.
    generalize (Hparent partition HgetParts); clear Hparent; intros Hparent; trivial.
    apply  nextEntryIsPPUpdateUserFlag' in  Hroot.
    apply Hparent; trivial.
    (** accessibleVAIsNotPartitionDescriptor **)
    unfold s'. 
    subst.
    apply accessibleVAIsNotPartitionDescriptorUpdateUserFlag with level
    (currentPartition s) currentPD ;trivial.
    assert(Hget : forall idx : index,
      StateLib.getIndexOfAddr list fstLevel = idx ->
      isPE ptConfigPagesList idx s /\ 
      getTableAddrRoot ptConfigPagesList PDidx (currentPartition s) list s) by trivial.     
    assert(isPE ptConfigPagesList (StateLib.getIndexOfAddr list fstLevel) s /\ 
            getTableAddrRoot ptConfigPagesList PDidx (currentPartition s) list s)
    as (_ & Hi).
    apply Hget; trivial.
    assumption.
    apply isAccessibleMappedPage with ptConfigPagesList;trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    (** accessibleChildPhysicalPageIsAccessibleIntoParent *)
    subst.
    assert(Htrue : accessibleChildPhysicalPageIsAccessibleIntoParent s) by intuition.
    unfold s'.
    assert(exists va : vaddr,
      isEntryVA childListSh1 (StateLib.getIndexOfAddr list fstLevel) va s /\
      beqVAddr defaultVAddr va = derivedRefChildListSh1) as 
      (vaInAncestor & HvaInAncestor & Hnotderived) by trivial.
    destruct Hcurentparent as (ancestor & Hancestor & Hancestornotnull).
    assert(Hancestorpart : In ancestor (getPartitions multiplexer s)).
    unfold parentInPartitionList in *.
    apply Hparent with (currentPartition s);trivial.
    assert(Hpde : partitionDescriptorEntry s) by trivial.
    unfold partitionDescriptorEntry in *.
    assert(exists entry : page, nextEntryIsPP ancestor PDidx entry s /\ entry <> defaultPage) as (pdAncestor & Hpdancestor & Hpdancesnotnull).
    apply Hpde;trivial.
    left;trivial.      
    apply accessibleChildPhysicalPageIsAccessibleIntoParentUpdate with  
    (currentPartition s) currentPD level;
    trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition;subst;trivial.
    clear Hpost.
    rename H into Hcond. 
    assert (H := conj (conj  Hpost1 Hfalse) Hsplit) .
    clear Hpost1 Hfalse Hsplit .
(** Propagated properties **)
    { intuition try eassumption. 
      * apply nextEntryIsPPUpdateUserFlag ; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP); clear H23; intros (H23 & _). 
        apply isPEUpdateUserFlag; assumption.
      *  assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * unfold s'.
        assert(ptRefChild <> ptConfigPagesList \/ idxRefChild  <>idxConfigPagesList).
        apply toApplyPageTablesOrIndicesAreDifferent with descChild list currentPart
          currentPD PDidx level isPE s; trivial.
         left;trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * assert(Hi3 : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi3 idx HP);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;  assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * apply entryUserFlagUpdateUserFlagSameValue;trivial.
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * apply entryUserFlagUpdateUserFlagSameValue;trivial.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi1 idx Hi2);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi1 idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * apply entryUserFlagUpdateUserFlagSameValue;trivial.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * apply nextEntryIsPPUpdateUserFlag;assumption.  
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1); clear H7; intros (H7 & H7').      
        apply isVEUpdateUserFlag; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                      isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChild)
                      by intuition.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                    isEntryVA ptPDChildSh1 idxPDChild va s /\ 
                    beqVAddr defaultVAddr va = derivedPDChild) by trivial. 
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
        isEntryVA ptSh1ChildFromSh1 idxSh1 va s /\ beqVAddr defaultVAddr va = derivedSh1Child) 
        by trivial.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr, isEntryVA childSh2 idxSh2 va s /\ 
                    beqVAddr defaultVAddr va = derivedSh2Child) by trivial.
      destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial. 
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert( Hi5 : exists va : vaddr,
                      isEntryVA childListSh1 idxConfigPagesList va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChildListSh1) by trivial.
        destruct Hi5 as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyPDChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phySh1Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phySh2Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyConfigPagesList (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial. 
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyDescChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial. 
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial. 
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial. 
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial. 
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.      
      * assert(HisAccess : isAccessibleMappedPageInParent currentPart list phyConfigPagesList s' =
          isAccessibleMappedPageInParent currentPart list phyConfigPagesList s).
          { unfold isAccessibleMappedPageInParent.
            unfold s'.
            simpl.
            rewrite getSndShadowUpdateUserFlag;trivial.
            case_eq( StateLib.getSndShadow currentPart (memory s));
            intros * Hsh2 ;trivial.
            assert( Hvirt :  getVirtualAddressSh2 p
    {|
    currentPartition := currentPartition s;
    memory := add ptConfigPagesList idxConfigPagesList
                (PE
                   {|
                   read := read entry;
                   write := write entry;
                   exec := exec entry;
                   present := present entry;
                   user := false;
                   pa := pa entry |}) (memory s) beqPage beqIndex |} list
                    =
                            getVirtualAddressSh2 p s list).
            { unfold getVirtualAddressSh2.
              assert(HnbL: Some level = StateLib.getNbLevel) by trivial.
              rewrite <- HnbL;trivial.
              rewrite getIndirectionUpdateUserFlag;trivial.
              destruct(getIndirection p list level (nbLevel - 1) s );trivial.
              simpl.
              rewrite readVirtualUpdateUserFlag;trivial. }
              rewrite Hvirt;trivial.
              case_eq (getVirtualAddressSh2 p s list);
              intros * Hvainances;trivial.
              rewrite getParentUpdateUserFlag;trivial.
              case_eq( StateLib.getParent currentPart (memory s)); 
              intros * HparentAcestor;trivial.
              rewrite getPdUpdateUserFlag.
              case_eq(StateLib.getPd p0 (memory s) );
              intros * Hpdparentances;trivial.
              assert( Haccessible : 
                        getAccessibleMappedPage p1
    {|
    currentPartition := currentPartition s;
    memory := add ptConfigPagesList idxConfigPagesList
                (PE
                   {|
                   read := read entry;
                   write := write entry;
                   exec := exec entry;
                   present := present entry;
                   user := false;
                   pa := pa entry |}) (memory s) beqPage beqIndex |} v= 
                        getAccessibleMappedPage p1 s v).
              { symmetry.
                
                unfold consistency in *.
                assert (Hparentpart : parentInPartitionList s ) by  intuition.
                unfold parentInPartitionList in *.
                assert(Hancestor : In p0 (getPartitions multiplexer s)).
                apply Hparentpart with currentPart;trivial.
                apply nextEntryIsPPgetParent; trivial.
                subst.
                apply getAccessibleMappedPageUpdateUserFlagDiffrentPartitions 
                with (currentPartition s) p0;trivial.
                intuition.
                assert(Hget : forall idx : index,
                        StateLib.getIndexOfAddr list fstLevel = idx ->
                        isPE ptConfigPagesList idx s /\ 
                        getTableAddrRoot ptConfigPagesList PDidx (currentPartition s) list s) by trivial.
                destruct Hget with (StateLib.getIndexOfAddr list fstLevel)
                as (Hpe & Hroot);
                trivial.

                admit. (**p0 <> currentPartition s : parent and child partition descriptors are different **)
                admit. (* disjoint (getConfigPages (currentPartition s) s) (getConfigPages p0 s)  between 
                          current partition and current partition's parent *) }
              assert(Haccess : accessibleChildPhysicalPageIsAccessibleIntoParent s).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold accessibleChildPhysicalPageIsAccessibleIntoParent in *.
              assert(Hpde : partitionDescriptorEntry s ).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }

              rewrite Haccessible;trivial.
              assumption. }
          rewrite HisAccess.
          assumption.
 (** New property **) 
      * unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptConfigPagesList, idxConfigPagesList) (ptConfigPagesList, idxConfigPagesList)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity. }
    intros [].
(** writeAccessibleRec : list **)
    eapply bindRev.
    eapply weaken.
    eapply WriteAccessibleRec.
    simpl.
    intros.
    split. 
    instantiate (42 := false).
    instantiate (41 := false).
    instantiate (40 := false).
    
        destruct H0 as (((H0  &Hc) 
        & Hd ) & He).

    assert(H0new := conj( conj H0 He )Hc ).    
      repeat rewrite and_assoc in H0new.

    unfold propagatedProperties.
    eapply H0new.
    instantiate(1:= phyConfigPagesList).
    instantiate(1:= idxConfigPagesList).
    instantiate(1:= ptConfigPagesList).
    intuition.
    subst.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in*.
    intuition.
    subst.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    intros.
    simpl.
(** writeAccessible : list  **)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply WP.writeAccessible.
    intros. simpl.
    assert (exists entry : Pentry,
      lookup ptRefChild idxRefChild (memory s) beqPage beqIndex = Some (PE entry)) as Hlookup.
    { apply isPELookupEq.
      unfold propagatedProperties in *.
      assert (forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isPE ptRefChild idx s /\ 
       getTableAddrRoot ptRefChild PDidx currentPart descChild s) as H1 by intuition.
      generalize (H1  idxRefChild);clear H1; intros H1.
      assert (StateLib.getIndexOfAddr descChild fstLevel = idxRefChild ) as H2 by intuition.
      apply H1 in H2. intuition. }
    destruct Hlookup as (entry & Hlookup).
    unfold propagatedProperties in *.
    exists entry ; split;trivial.
(** Here the first shadow is still accessible, so we summarize this property  **)
    assert(HpdChildaccess : getAccessibleMappedPage currentPD s descChild = Some phyDescChild).
    { intuition.
      assert(Heqentry : pa entry =phyDescChild).
      apply isEntryPageLookupEq with ptRefChild idxRefChild s;subst;trivial.
      rewrite <- Heqentry in *.
      apply isAccessibleMappedPage with ptRefChild;subst;trivial.
      repeat rewrite andb_true_iff in Hlegit.
      intuition. subst;trivial.
      repeat rewrite andb_true_iff in Hlegit.
      intuition. 
      subst;trivial. }
    assert(Hcurparts : In currentPart (getPartitions multiplexer s)).
    { unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      subst.
      assumption. }
    assert(Hcurpd : StateLib.getPd currentPart (memory s) = Some currentPD).
    { intuition. subst.
      apply nextEntryIsPPgetPd;trivial. }
    assert (Hpde : partitionDescriptorEntry s).
    { unfold consistency in *. intuition. }
    unfold partitionDescriptorEntry in *.
    generalize (Hpde currentPart Hcurparts PPRidx); clear Hpde; intros Hpde.
    
    assert(Hcurentparent : (exists entry : page, nextEntryIsPP currentPart PPRidx entry s /\
     entry <> defaultPage) ).
    { apply Hpde.
      do 4 right;left;trivial. }
    clear Hpde.
    assert (Hpde : partitionDescriptorEntry s).
    { unfold consistency in *. intuition. }
    unfold partitionDescriptorEntry in *.
    generalize (Hpde currentPart Hcurparts sh2idx); clear Hpde; intros Hpde.
    
    assert(Hcurrentsh2 : (exists entry : page, nextEntryIsPP currentPart sh2idx entry s /\
     entry <> defaultPage) ).
    { apply Hpde.
      do 2 right;left;trivial. }
    clear Hpde.

(** Here the first shadow is still accessible, so we prove that in all ancestor this physical 
page is already accessible **)
     assert(Hisaccessible : isAccessibleMappedPageInParent currentPart descChild phyDescChild s = true).
           { assert(Hcons : consistency s).
        { unfold propagatedProperties in *.
          intuition. }
        unfold consistency in Hcons.
        assert(Haccess : accessibleChildPhysicalPageIsAccessibleIntoParent s) by intuition.
        unfold accessibleChildPhysicalPageIsAccessibleIntoParent in Haccess.
        apply Haccess with currentPD;intuition. }
    
      do 26 rewrite <- and_assoc in H0.
    destruct H0 as (Hi & Hsplit). 
    destruct Hi as (Hi & Hfalse). 
    try repeat rewrite and_assoc in Hi.
    assert (Hpost1 := conj  Hi Hsplit)  .

    assert (Hpost := conj Hpost1 Hisaccessible).
    pattern s in Hpost.
    match type of Hpost with 
    | ?HT s => instantiate (1 := fun tt s => HT s /\ 
                entryUserFlag ptRefChild idxRefChild false s)
    end.
    simpl.
    set (s' := {|
    currentPartition := currentPartition s;
    memory := add  ptRefChild idxRefChild
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
    do 8 rewrite and_assoc.             
    split. 
  (** partitionsIsolation **) 
    assert (partitionsIsolation s ) as Hiso. intuition.
    clear Hpost Hsplit.
    unfold partitionsIsolation in *.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartitions. clear Hpartitions.
    intros.
    generalize (Hiso parent child1 child2); clear Hiso; intros Hiso. 
    assert(getChildren parent s' = getChildren parent s) as Hchildren.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite Hchildren in H2, H1. clear Hchildren.
    assert (getUsedPages child1 s'= getUsedPages child1 s) as Hch1used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch1used. clear Hch1used.
    assert (getUsedPages child2 s' = getUsedPages child2 s) as Hch2used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch2used. clear Hch2used.
    apply Hiso; trivial.
    split.
  (** kernelDataIsolation **)
    assert (kernelDataIsolation s) as HAncesiso. intuition.
    unfold kernelDataIsolation in *.
    intros.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartitions in *.
    clear Hpartitions.
    assert(  (getConfigPages partition2 s') = (getConfigPages partition2 s)) as Hconfig.
    apply getConfigPagesUpdateUserFlag; trivial.
    rewrite Hconfig. clear Hconfig.
    assert (incl (getAccessibleMappedPages partition1 s') (getAccessibleMappedPages partition1 s)).
    apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
    unfold disjoint in *.
    intros.
    unfold incl in *.
    apply HAncesiso with partition1; trivial.
    apply H2; trivial.
(** Vertical Sharing **)
    split. unfold verticalSharing in *.
    assert (Hvs : verticalSharing s)  by intuition.
    clear Hpost Hsplit.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartitions. clear Hpartitions.
    intros.
    generalize (Hvs parent child); clear Hvs; intros Hvs.
    assert (getUsedPages child s' = getUsedPages child s) as Husedpage.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite   Husedpage.
    assert ( getMappedPages parent s' = getMappedPages parent s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd parent (memory s') = StateLib.getPd parent (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd parent (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. apply Hvs;trivial.
    assert (getChildren parent s' = getChildren parent s) as Hchild.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite <- Hchild. assumption.
    split.
  (** Consistency **) 
    assert (Hcons : consistency s) by intuition. 
    clear Hsplit.     
    unfold consistency in *.
    split. apply partitionDescriptorEntryUpdateUserFlag;trivial.
    intuition.
    destruct Hcons as (Hpe & Hpd & Hsh1 & Hsh2 & HcurpartdescChild & 
    Hnodupmapped & Hnodupconfig & Hparent & Hsh1struct).
    clear Hpost1 Hi.
    repeat split; try  apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
    unfold currentPartitionInPartitionsList in *.
    simpl in *. subst. 
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartitions. assumption.
    unfold noDupMappedPagesList in *.
    intros partition HgetPartnewstate.
    assert ( getMappedPages partition s' = getMappedPages partition s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd partition (memory s') = StateLib.getPd partition (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd partition (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. 
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag;trivial.
    rewrite HgetPart in HgetPartnewstate.
    apply Hnodupmapped;assumption.
    apply getIndirectionsNoDupUpdateUserFlag; trivial.
    unfold parentInPartitionList in *.
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite HgetPart.
    intros partition HgetParts parent Hroot.
    generalize (Hparent partition HgetParts); clear Hparent; intros Hparent; trivial.
    apply  nextEntryIsPPUpdateUserFlag' in  Hroot.
    apply Hparent; trivial.
    (** accessibleVAIsNotPartitionDescriptor **)
    unfold s'. 
    subst.
    apply accessibleVAIsNotPartitionDescriptorUpdateUserFlag with level
    (currentPartition s) currentPD ;trivial.
    assert(Hget : forall idx : index,
      StateLib.getIndexOfAddr descChild fstLevel = idx ->
      isPE ptRefChild idx s /\ 
      getTableAddrRoot ptRefChild PDidx (currentPartition s) descChild s) by trivial.     
    assert(isPE ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) s /\ 
            getTableAddrRoot ptRefChild PDidx (currentPartition s) descChild s)
    as (_ & Hi).
    apply Hget; trivial.
    assumption.
    apply isAccessibleMappedPage with ptRefChild;trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    (** accessibleChildPhysicalPageIsAccessibleIntoParent *)
    subst.
    assert(Htrue : accessibleChildPhysicalPageIsAccessibleIntoParent s) by intuition.
    unfold s'.
    assert(exists va : vaddr,
        isEntryVA ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) va s /\
        beqVAddr defaultVAddr va = derivedRefChild) as 
      (vaInAncestor & HvaInAncestor & Hnotderived) by trivial.
    destruct Hcurentparent as (ancestor & Hancestor & Hancestornotnull).
    assert(Hancestorpart : In ancestor (getPartitions multiplexer s)).
    unfold parentInPartitionList in *.
    apply Hparent with (currentPartition s);trivial.
    assert(Hpde : partitionDescriptorEntry s) by trivial.
    unfold partitionDescriptorEntry in *.
    assert(exists entry : page, nextEntryIsPP ancestor PDidx entry s /\ entry <> defaultPage) as (pdAncestor & Hpdancestor & Hpdancesnotnull).
    apply Hpde;trivial.
    left;trivial.      
    apply accessibleChildPhysicalPageIsAccessibleIntoParentUpdate with  
    (currentPartition s) currentPD level;
    trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition;subst;trivial.
    clear Hpost.
    rename H into Hcond. 
(** Propagated properties **)
    { intuition try eassumption. 
      * apply nextEntryIsPPUpdateUserFlag ; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP); clear H23; intros (H23 & _). 
        apply isPEUpdateUserFlag; assumption.
      *  assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert(Hi3 : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi3 idx HP);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;  assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial.  
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * apply entryUserFlagUpdateUserFlagSameValue;trivial.
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * apply entryUserFlagUpdateUserFlagSameValue;trivial.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi1 idx Hi2);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi1 idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * apply entryUserFlagUpdateUserFlagSameValue;trivial.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * apply entryUserFlagUpdateUserFlagSameValue;trivial.
      * apply nextEntryIsPPUpdateUserFlag;assumption.  
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1); clear H7; intros (H7 & H7').      
        apply isVEUpdateUserFlag; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                      isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChild)
                      by intuition.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                    isEntryVA ptPDChildSh1 idxPDChild va s /\ 
                    beqVAddr defaultVAddr va = derivedPDChild) by trivial. 
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
        isEntryVA ptSh1ChildFromSh1 idxSh1 va s /\ beqVAddr defaultVAddr va = derivedSh1Child) 
        by trivial.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr, isEntryVA childSh2 idxSh2 va s /\ 
                    beqVAddr defaultVAddr va = derivedSh2Child) by trivial.
      destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial. 
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert( Hi5 : exists va : vaddr,
                      isEntryVA childListSh1 idxConfigPagesList va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChildListSh1) by trivial.
        destruct Hi5 as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse' : In phyPDChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse' : In phySh1Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse' : In phySh2Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse' : In phyConfigPagesList (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial. 
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse' : In phyDescChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial. 
      * assert(HisAccess : isAccessibleMappedPageInParent currentPart descChild phyDescChild s' =
          isAccessibleMappedPageInParent currentPart descChild phyDescChild s).
          { unfold isAccessibleMappedPageInParent.
            unfold s'.
            simpl.
            rewrite getSndShadowUpdateUserFlag;trivial.
            case_eq( StateLib.getSndShadow currentPart (memory s));
            intros * Hsh2 ;trivial.
            assert( Hvirt :  getVirtualAddressSh2 p
    {|
    currentPartition := currentPartition s;
    memory := add ptRefChild idxRefChild
                (PE
                   {|
                   read := read entry;
                   write := write entry;
                   exec := exec entry;
                   present := present entry;
                   user := false;
                   pa := pa entry |}) (memory s) beqPage beqIndex |} descChild
                    =
                            getVirtualAddressSh2 p s descChild).
            { unfold getVirtualAddressSh2.
              assert(HnbL: Some level = StateLib.getNbLevel) by trivial.
              rewrite <- HnbL;trivial.
              rewrite getIndirectionUpdateUserFlag;trivial.
              destruct(getIndirection p descChild level (nbLevel - 1) s );trivial.
              simpl.
              rewrite readVirtualUpdateUserFlag;trivial. }
              rewrite Hvirt;trivial.
              case_eq (getVirtualAddressSh2 p s descChild);
              intros * Hvainances;trivial.
              rewrite getParentUpdateUserFlag;trivial.
              case_eq( StateLib.getParent currentPart (memory s)); 
              intros * HparentAcestor;trivial.
              rewrite getPdUpdateUserFlag.
              case_eq(StateLib.getPd p0 (memory s) );
              intros * Hpdparentances;trivial.
              assert( Haccessible : 
                        getAccessibleMappedPage p1
    {|
    currentPartition := currentPartition s;
    memory := add ptRefChild idxRefChild
                (PE
                   {|
                   read := read entry;
                   write := write entry;
                   exec := exec entry;
                   present := present entry;
                   user := false;
                   pa := pa entry |}) (memory s) beqPage beqIndex |} v= 
                        getAccessibleMappedPage p1 s v).
              { symmetry.
                
                unfold consistency in *.
                assert (Hparentpart : parentInPartitionList s ) by  intuition.
                unfold parentInPartitionList in *.
                assert(Hancestor : In p0 (getPartitions multiplexer s)).
                apply Hparentpart with currentPart;trivial.
                apply nextEntryIsPPgetParent; trivial.
                subst.
                apply getAccessibleMappedPageUpdateUserFlagDiffrentPartitions 
                with (currentPartition s) p0;trivial.
                intuition.
                assert(Hget : forall idx : index,
                        StateLib.getIndexOfAddr descChild fstLevel = idx ->
                        isPE ptRefChild idx s /\ 
                        getTableAddrRoot ptRefChild PDidx (currentPartition s) descChild s) by trivial.
                destruct Hget with (StateLib.getIndexOfAddr descChild fstLevel)
                as (Hpe & Hroot);
                trivial.

                admit. (**p0 <> currentPartition s : parent and child partition descriptors are different **)
                admit. (* disjoint (getConfigPages (currentPartition s) s) (getConfigPages p0 s)  between 
                          current partition and current partition's parent *) }
              assert(Haccess : accessibleChildPhysicalPageIsAccessibleIntoParent s).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold accessibleChildPhysicalPageIsAccessibleIntoParent in *.
              assert(Hpde : partitionDescriptorEntry s ).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }

              rewrite Haccessible;trivial.
              assumption. }
          rewrite HisAccess.
          assumption.
(** New property **) 
      * unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptRefChild, idxRefChild) (ptRefChild, idxRefChild)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity. }
    intros [].
(** writeAccessibleRec : descChild **)
    eapply bindRev.
    eapply weaken.
    eapply WriteAccessibleRec.
    simpl.
    intros.
    split. 
    instantiate (43 := false).
    instantiate (42 := false).
    instantiate (41 := false).
    instantiate (40 := false).
    
        destruct H0 as (((H0  &Hc) 
        & Hd ) & He).

    assert(H0new := conj( conj H0 He )Hc ).    
      repeat rewrite and_assoc in H0new.

    unfold propagatedProperties.
    eapply H0new.
    instantiate(1:= phyDescChild).
    instantiate(1:= idxRefChild).
    instantiate(1:= ptRefChild).
    intuition.
    subst.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in*.
    intuition.
    subst.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    intros.
    simpl.
(** IndexZero **)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply Invariants.Index.zero.
    simpl.
    intros.
    pattern s in H0.
    eassumption.
    intros zero. simpl. 
(** initPEntryTable **)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply conjPrePost.
    eapply initPEntryTablePropagateProperties1.
    eapply initPEntryTableNewProperty.
    { intros. simpl.
      split. split.
      eassumption.
      unfold propagatedProperties in *.
      split. intuition. intuition.
      intros.
      assert (zero = CIndex 0) as Hzero.
      intuition.
      subst.
      unfold CIndex in H1.
      case_eq (lt_dec 0 tableSize).
      intros.
      rewrite H2 in H1.
      simpl in *. omega.
      intros.
      contradict H2.
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. }
    intros resinittablepd.
    simpl.
(** initPEntryTable **)    
    eapply WP.bindRev.
    eapply preAndPost.
    eapply WP.weaken.
    eapply conjPrePost.
    eapply initPEntryTablePropagateProperties1.
    eapply initPEntryTableNewProperty.
    { intros. simpl.
      split. split.
      eassumption.
      unfold propagatedProperties in *.
      split. intuition. intuition.
      intros.
      assert (zero = CIndex 0) as Hzero.
      intuition.
      subst.
      unfold CIndex in H1.
      case_eq (lt_dec 0 tableSize).
      intros.
      rewrite H2 in H1.
      simpl in *. omega.
      intros.
      contradict H2.
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. }
    eapply weaken.
    eapply initPEntryTablePropagateProperties2.
    intros.
    simpl.
    destruct H0 as ((H0 & Hzero) & Hphypd).
    split.
    split;
    eassumption.
    unfold propagatedProperties in *.
    assert(Hget1 :forall idx : index,
      StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
      isPE ptSh1Child idx s /\ 
      getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
    assert(Hget2 : forall idx : index,
      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
      isPE ptPDChild idx s /\ 
      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by intuition.
    intuition trivial.
    instantiate (1:= ptSh1Child); assumption.
    instantiate (1:= ptPDChild); assumption.
    instantiate (1:= currentPart); assumption.
    subst.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *.
    intuition.
    instantiate (1 := shadow1).
    subst.
    assumption.
    instantiate (1 := pdChild).
    subst.
    assumption.
    apply Hget1; trivial.
    assert(Hidx : StateLib.getIndexOfAddr shadow1 fstLevel = idxSh1) by trivial.
    generalize (Hget1 idxSh1 Hidx);clear Hget1 ; intros (_ & Hhet1); assumption.
    apply Hget2; trivial.
    assert(Hidx : StateLib.getIndexOfAddr pdChild fstLevel = idxPDChild) by trivial.
    generalize (Hget2 idxPDChild Hidx);clear Hget1 ; intros (_ & Hhet1); assumption.
    assumption.
    assert (presentSh1 = true).
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst.
    assumption.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst.
    assumption.
(** initPEntryTable **) 
    intros resinittablesh1. simpl.
    eapply WP.bindRev.
    { eapply preAndPost.
      + eapply preAndPost.
        - eapply WP.weaken.
          eapply conjPrePost.
          eapply initPEntryTablePropagateProperties1.
          eapply initPEntryTableNewProperty.
          { intros. simpl.
            split. split.
            eassumption.
            unfold propagatedProperties in *.
            split. intuition. intuition.
            intros.
            assert (zero = CIndex 0) as Hzero.
            intuition.
            subst.
            unfold CIndex in H1.
            case_eq (lt_dec 0 tableSize).
            intros.
            rewrite H2 in H1.
            simpl in *. omega.
            intros.
            contradict H2.
            assert (tableSize > tableSizeLowerBound).
            apply tableSizeBigEnough.
            unfold tableSizeLowerBound in *.
            omega. }
        - eapply weaken.
          eapply initPEntryTablePropagateProperties2.
          intros.
          simpl.
          destruct H0 as ((H0 & Hzero) & Hphypd).
          split.
          split;
          eassumption.
          unfold propagatedProperties in *.
          assert(Hget1 :forall idx : index,
            StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
            isPE ptSh2Child idx s /\ 
            getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by intuition.
          assert(Hget2 : forall idx : index,
            StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
            isPE ptSh1Child idx s /\ 
            getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
          intuition trivial.
          instantiate (1:= ptSh2Child); assumption.
          instantiate (1:= ptSh1Child); assumption.
          instantiate (1:= currentPart); assumption.
          subst.
          unfold consistency in *.
          unfold currentPartitionInPartitionsList in *.
          intuition.
          instantiate (1 := shadow2).
          subst.
          assumption.
          instantiate (1 := shadow1).
          subst.
          assumption.
          apply Hget1; trivial.
          assert(Hidx : StateLib.getIndexOfAddr shadow2 fstLevel = idxSh2) by trivial.
          generalize (Hget1 idxSh2 Hidx);clear Hget1 ; intros (_ & Hhet1); assumption.
          apply Hget2; trivial.
          assert(Hidx : StateLib.getIndexOfAddr shadow1 fstLevel = idxSh1) by trivial.
          generalize (Hget2 idxSh1 Hidx);clear Hget1 ; intros (_ & Hhet1); assumption.
          assumption.
          assert (presentSh2 = true).
          repeat rewrite andb_true_iff in Hlegit.
          intuition.
          subst.
          assumption.
          repeat rewrite andb_true_iff in Hlegit.
          intuition.
          subst.
          assumption.
    + rewrite andAssocHT .
      apply permutHT.
      rewrite  <- andAssocHT.
      apply preAnd.
      eapply weaken.
      eapply initPEntryTablePropagateProperties2.
      intros.
      simpl.
      destruct H0 as ((H0  & Hzero) & Hphypd).
      split.
      split;
      eassumption.
      unfold propagatedProperties in *.
      assert(Hget1 :forall idx : index,
        StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
        isPE ptSh2Child idx s /\ 
        getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by intuition.
      assert(Hget2 : forall idx : index,
        StateLib.getIndexOfAddr pdChild fstLevel = idx ->
        isPE ptPDChild idx s /\ 
        getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by intuition.
      intuition trivial.
      instantiate (1:= ptSh2Child); assumption.
      instantiate (1:= ptPDChild); assumption.
      instantiate (1:= currentPart); assumption.
      subst.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      instantiate (1 := shadow2).
      subst.
      assumption.
      instantiate (1 := pdChild).
      subst.
      assumption.
      apply Hget1; trivial.
      assert(Hidx : StateLib.getIndexOfAddr shadow2 fstLevel = idxSh2) by trivial.
      generalize (Hget1 idxSh2 Hidx);clear Hget1 ; intros (_ & Hhet1); assumption.
      apply Hget2; trivial.
      assert(Hidx : StateLib.getIndexOfAddr pdChild fstLevel = idxPDChild) by trivial.
      generalize (Hget2 idxPDChild Hidx);clear Hget1 ; intros (_ & Hhet1); assumption.
      assumption.
      assert (presentSh2 = true).
      repeat rewrite andb_true_iff in Hlegit.
      intuition.
      subst.
      assumption.
      repeat rewrite andb_true_iff in Hlegit.
      intuition.
      subst.
      assumption. }
    intros resinittablesh2. simpl.
(** initConfigPagesList **)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply conjPrePost.
    eapply initConfigPagesListPropagateProperties.

    intuition.
    eapply initConfigPagesListNewProperty.
    simpl; intros.
    split.
    rewrite <- and_assoc. 
    split.
    repeat rewrite andb_true_iff in Hlegit.
    repeat rewrite and_assoc in Hlegit.
    destruct Hlegit as (H1 & _ & H2 & _ & H3 & _ & H4 & _ & H5 & _ ).
    subst.
    apply H0.
    left. intuition.
    split.
    left;intuition.
    split.
    intros.
    assert (zero = CIndex 0) as Hzero.
    intuition.
    subst. (* 
    left; trivial.
    assert (zero = CIndex 0) as Hzero.
    intuition.
    subst.
    split; intros. *)
    unfold CIndex in H3.
    case_eq (lt_dec 0 tableSize).
    intros.
    rewrite H4 in H3.
    simpl in *. omega.
    intros.
    contradict H4.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    intros.
    intuition; subst.
    unfold CIndex in H2.
    case_eq (lt_dec 0 tableSize).
    intros.
    rewrite H3 in H2.
    simpl in *. omega.
    intros.
    contradict H.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    intros [].
    simpl.
(** getDefaultVAddr **)
    eapply bindRev.
    eapply weaken.
    eapply Invariants.getDefaultVAddr.
    intros.
    simpl.
    pattern s in H0.
    eapply H0.
    simpl.
    intros nullv. 
(** getPRidx **)
    eapply bindRev.
    eapply weaken.
    eapply Invariants.getPRidx.
    intros.
    simpl.
    pattern s in H0.
    eapply H0.
    simpl.
    intros idxPR.
(** getPDidx **)
    eapply bindRev.
    eapply weaken.
    eapply Invariants.getPDidx.
    intros.
    simpl.
    repeat rewrite and_assoc in H0. 
    pattern s in H0.
    eapply H0.
    simpl.
    intros idxPD.
(** getSh1idx **)
    eapply bindRev.
    eapply weaken.
    eapply Invariants.getSh1idx.
    intros.
    simpl.
    repeat rewrite and_assoc in H0. 
    pattern s in H0.
    eapply H0.
    simpl.
    intros idxSH1.
(** getSh2idx **)
    eapply bindRev.
    eapply weaken.
    eapply Invariants.getSh2idx.
    intros.
    simpl.
    repeat rewrite and_assoc in H0. 
    pattern s in H0.
    eapply H0.
    simpl.
    intros idxSH2.
(** getSh3idx **)
    eapply bindRev.
    eapply weaken.
    eapply Invariants.getSh3idx.
    intros.
    simpl.
    repeat rewrite and_assoc in H0. 
    pattern s in H0.
    eapply H0.
    simpl.
    intros idxSH3.
(** getPRPidx **)
    eapply bindRev.
    eapply weaken.
    eapply Invariants.getPPRidx.
    intros.
    simpl.
    repeat rewrite and_assoc in H0. 
    pattern s in H0.
    eapply H0.
    simpl.
    intros idxPPR.
(** updatePartitionDescriptor : add the partition descriptor itself *)
    eapply bindRev.
    eapply WP.weaken.
    eapply conjPrePost.
    eapply updatePartitionDescriptorPropagatedProperties.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    eapply updatePartitionDescriptorNewProperty.
    simpl.
    intros.
    split.
    rewrite <- and_assoc.
    split.
    eassumption.
    trivial.
    simpl.
    instantiate(1:= ptRefChild).
    instantiate(1:= descChild).
    instantiate(1:=  idxRefChild).
    unfold propagatedProperties in *.
    assert(Hget1 :forall idx : index,
                  StateLib.getIndexOfAddr descChild fstLevel = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild PDidx currentPart descChild s) by intuition.
    intuition.
    apply Hget1; trivial.
    assert(Hidx : StateLib.getIndexOfAddr descChild fstLevel = idxRefChild) by trivial.
    generalize (Hget1 idxRefChild Hidx);clear Hget1 ; intros (_ & Hhet1).
    subst. assumption.
    subst. assumption.
    unfold propagatedProperties in *.
    unfold consistency in *.
    intuition.
    subst.
    assert (Hpde : partitionDescriptorEntry s) by trivial.
    unfold  partitionDescriptorEntry in *.
    assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
    unfold currentPartitionInPartitionsList in *.
    intuition.
    apply Hpde with (currentPartition s)  PRidx in Hcur.
    intuition.
    repeat right; trivial.
    assert (idxPR = PRidx) by intuition.
    subst.
    unfold propagatedProperties in *.
    unfold consistency in *.
    assert (Hpde : partitionDescriptorEntry s) by intuition.
    unfold partitionDescriptorEntry in *.
    intuition.
    subst.
    assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
    unfold currentPartitionInPartitionsList in *. 
    intuition.
    apply Hpde with (currentPartition s) PRidx   in Hcur.
    intuition.
    try repeat right; trivial.
    intros [].
(** updatePartitionDescriptor : add the page directory into the partition descriptor *)
    eapply WP.bindRev.
    eapply preAndPost.
    eapply WP.weaken.
    eapply conjPrePost.
    eapply updatePartitionDescriptorPropagatedProperties.
    intuition.
    eapply updatePartitionDescriptorNewProperty.
    simpl.
    intros.
    split.
    split.
    destruct H0.
    eassumption.
    split.
    destruct H0.
    eassumption.
    instantiate(1:= ptRefChild).
    instantiate(1:= descChild).
    instantiate(1:=  idxRefChild).
    unfold propagatedProperties in *.
    intuition.
    assert(Hget1 :forall idx : index,
                  StateLib.getIndexOfAddr descChild fstLevel = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild PDidx currentPart descChild s) by intuition.
    intuition.
    apply Hget1; trivial.
    assert(Hget1 :forall idx : index,
                  StateLib.getIndexOfAddr descChild fstLevel = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild PDidx currentPart descChild s) by intuition.
    intuition.
    assert(Hidx : StateLib.getIndexOfAddr descChild fstLevel = idxRefChild) by trivial.
    generalize (Hget1 idxRefChild Hidx);clear Hget1 ; intros (_ & Hhet1).
    subst. assumption.
    subst. assumption.
    unfold propagatedProperties in *.
    unfold consistency in *.
    intuition.
    subst.
    assert (Hpde : partitionDescriptorEntry s) by trivial.
    unfold  partitionDescriptorEntry in *.
    assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
    unfold currentPartitionInPartitionsList in *.
    intuition.
    apply Hpde with (currentPartition s)  PDidx in Hcur.
    intuition.
    left; trivial.
    unfold propagatedProperties in *.
    unfold consistency in *.
    intuition.
    subst.
    assert (Hpde : partitionDescriptorEntry s) by trivial.
    unfold  partitionDescriptorEntry in *.
    assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
    unfold currentPartitionInPartitionsList in *.
    intuition.
    apply Hpde with (currentPartition s)  PDidx in Hcur.
    intuition.
    left; trivial.
    simpl.
    eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxPD < tableSize - 1 /\ idxPR < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) PDidx   in Hcur.
      intuition.
      left; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) PRidx   in Hcur.
      intuition.
      try repeat right; trivial. }
    destruct H0.
    destruct H0.  
    destruct H0 as (H0 & _ & H4).
    intuition.
    assert(Hnoteq : idxPR <> idxPD).
    { subst.
      unfold PDidx. unfold PRidx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    now contradict Hnoteq.
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PRidx + 1) tableSize); intros * Hc2.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (PRidx + 1) tableSize ); intros * Hc3 Hc4.
    contradict Hc4.
    subst.
    unfold PDidx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 2 tableSize); intros * Hc5.
    unfold not; intros Hc6.
    inversion Hc6 as [Hc7].
    unfold CIndex in Hc7.
    case_eq(lt_dec 0 tableSize); intros * Hc8; rewrite Hc8 in *.
    inversion Hc6.
    simpl in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    subst.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
    assert(Hnoteq : idxPR <> idxPD).
    { subst.
      unfold PDidx. unfold PRidx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
   
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PDidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PDidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PDidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (PDidx + 1) tableSize ); intros.
    contradict H13.
    subst.
    unfold PDidx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 0 tableSize); intros.
    unfold not; intros.
    inversion H14.
    unfold CIndex in H16.
    case_eq(lt_dec 0 tableSize); intros; rewrite H15 in *.
    inversion H16.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
    omega.
    simpl.
    intros [].
(** updatePartitionDescriptor : add the page directory into the partition descriptor *)
eapply WP.bindRev.
    eapply preAndPost.
        eapply preAndPost.
    eapply WP.weaken.
    eapply conjPrePost.
    eapply updatePartitionDescriptorPropagatedProperties.
    intuition.
    eapply updatePartitionDescriptorNewProperty.
    simpl.
    intros.
    repeat rewrite and_assoc in H0.
    repeat rewrite and_assoc.
    destruct H0.
    destruct H1.
    split. 
    eapply H0.
    instantiate(1:= ptRefChild).
    instantiate(1:= descChild).
    instantiate(1:=  idxRefChild).
    instantiate(1:=  idxPPR).
    instantiate(1:= idxSH3).
    instantiate(1:= idxSH2).
    instantiate(1:=  idxSH1).
    instantiate(1:=  idxPD).
    instantiate(1:=  idxPR).
    instantiate(1:=  nullv).
    instantiate(1:=  zero).
    unfold propagatedProperties in *.
    intuition.
    assert(Hget1 :forall idx : index,
                  StateLib.getIndexOfAddr descChild fstLevel = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild PDidx currentPart descChild s) by intuition.
    intuition.
    apply Hget1; trivial.
    assert(Hget1 :forall idx : index,
                  StateLib.getIndexOfAddr descChild fstLevel = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild PDidx currentPart descChild s) by intuition.
    intuition.
    assert(Hidx : StateLib.getIndexOfAddr descChild fstLevel = idxRefChild) by trivial.
    generalize (Hget1 idxRefChild Hidx);clear Hget1 ; intros (_ & Hhet1).
    subst. assumption.
    subst. assumption.
    unfold propagatedProperties in *.
    unfold consistency in *.
    intuition.
    subst.
    assert (Hpde : partitionDescriptorEntry s) by trivial.
    unfold  partitionDescriptorEntry in *.
    assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
    unfold currentPartitionInPartitionsList in *.
    intuition.
    apply Hpde with (currentPartition s)  sh1idx in Hcur.
    intuition.
    right;left; trivial.
    unfold propagatedProperties in *.
    unfold consistency in *.
    intuition.
    subst.
    assert (Hpde : partitionDescriptorEntry s) by trivial.
    unfold  partitionDescriptorEntry in *.
    assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
    unfold currentPartitionInPartitionsList in *.
    intuition.
    apply Hpde with (currentPartition s) sh1idx  in Hcur.
    intuition.
    right; left; trivial.
    simpl.
    simpl.
    eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxPD < tableSize - 1 /\ idxSH1 < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) PDidx   in Hcur.
      intuition.
      left; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) sh1idx   in Hcur.
      intuition.
      right;left;trivial. }
    destruct H0.
    destruct H0.  
    destruct H0 as (H0 &  H4).
    intuition.
    assert(Hnoteq : idxPD <> idxSH1).
    { subst.
      unfold PDidx. unfold sh1idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    now contradict Hnoteq.
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PDidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PDidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PDidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (PDidx + 1) tableSize ); intros.
    contradict H13.
    subst.
    unfold sh1idx. unfold PDidx.
    unfold CIndex at 3.
    case_eq (lt_dec 4 tableSize); intros.
    unfold not; intros.
    inversion H14.
    unfold CIndex in H16.
    case_eq(lt_dec 2 tableSize); intros; rewrite H15 in *.
    inversion H16.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
    assert(Hnoteq : idxPR <> idxPD).
    { subst.
      unfold PDidx. unfold PRidx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh1idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh1idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh1idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (sh1idx + 1) tableSize ); intros.
    contradict H13.
    subst.
    unfold PDidx. unfold sh1idx.
    unfold CIndex at 3.
    case_eq (lt_dec 2 tableSize); intros.
    unfold not; intros.
    inversion H14.
    unfold CIndex in H16.
    case_eq(lt_dec 4 tableSize); intros; rewrite H15 in *.
    inversion H16.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
      eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxPR < tableSize - 1 /\ idxSH1 < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) PRidx   in Hcur.
      intuition.
      repeat right ; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) sh1idx   in Hcur.
      intuition.
      right;left;trivial. }
    destruct H0.
    destruct H0. 
    destruct H0.  
    destruct H0 as (H0 &  H5).
    intuition.
    assert(Hnoteq : idxPR <> idxSH1).
    { subst.
      unfold PRidx. unfold sh1idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    now contradict Hnoteq.
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (PRidx + 1) tableSize ); intros.
    contradict H15.
    subst.
    unfold sh1idx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 4 tableSize); intros.
    unfold not; intros.
    inversion H16.
    unfold CIndex in H18.
    case_eq(lt_dec 0 tableSize); intros; rewrite H17 in *.
    inversion H18.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
    assert(Hnoteq : idxPR <> idxSH1).
    { subst.
      unfold sh1idx. unfold PRidx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh1idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh1idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh1idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (sh1idx + 1) tableSize ); intros.
    contradict H15.
    subst.
    unfold PRidx. unfold sh1idx.
    unfold CIndex at 3.
    case_eq (lt_dec 0 tableSize); intros.
    unfold not; intros.
    inversion H16.
    unfold CIndex in H18.
    case_eq(lt_dec 4 tableSize); intros; rewrite H17 in *.
    inversion H16.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.  
    omega.
    
    simpl.
    intros [].
(** updatePartitionDescriptor : add the page directory into the partition descriptor *)
    eapply WP.bindRev.
    eapply preAndPost.
    eapply preAndPost.
    eapply preAndPost.    
    eapply WP.weaken.
    eapply conjPrePost.
    eapply updatePartitionDescriptorPropagatedProperties.
    intuition.
    eapply updatePartitionDescriptorNewProperty.
    simpl.
    intros.
    repeat rewrite and_assoc in H0.
    repeat rewrite and_assoc.
    destruct H0.
    destruct H1.
    split.
    eapply H0.
    instantiate(1:= ptRefChild).
    instantiate(1:= descChild).
    instantiate(1:=  idxRefChild).
    instantiate(1:=  idxPPR).
    instantiate(1:= idxSH3).
    instantiate(1:= idxSH2).
    instantiate(1:=  idxSH1).
    instantiate(1:=  idxPD).
    instantiate(1:=  idxPR).
        instantiate(1:=  nullv).
    instantiate(1:=  zero).
    unfold propagatedProperties in *.
    intuition.
    assert(Hget1 :forall idx : index,
                  StateLib.getIndexOfAddr descChild fstLevel = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild PDidx currentPart descChild s) by intuition.
    intuition.
    apply Hget1; trivial.
    assert(Hget1 :forall idx : index,
                  StateLib.getIndexOfAddr descChild fstLevel = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild PDidx currentPart descChild s) by intuition.
    intuition.
    assert(Hidx : StateLib.getIndexOfAddr descChild fstLevel = idxRefChild) by trivial.
    generalize (Hget1 idxRefChild Hidx);clear Hget1 ; intros (_ & Hhet1).
    subst. assumption.
    subst. assumption.
    unfold propagatedProperties in *.
    unfold consistency in *.
    intuition.
    subst.
    assert (Hpde : partitionDescriptorEntry s) by trivial.
    unfold  partitionDescriptorEntry in *.
    assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
    unfold currentPartitionInPartitionsList in *.
    intuition.
    apply Hpde with (currentPartition s)  sh2idx in Hcur.
    subst.
    intuition.
    right;right;left; trivial.
    unfold propagatedProperties in *.
    unfold consistency in *.
    intuition.
    subst.
    assert (Hpde : partitionDescriptorEntry s) by trivial.
    unfold  partitionDescriptorEntry in *.
    assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
    unfold currentPartitionInPartitionsList in *.
    intuition.
    apply Hpde with (currentPartition s) sh2idx  in Hcur.
    intuition.
    right;right; left; trivial.
    simpl.
    simpl.
    eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxSH2 < tableSize - 1 /\ idxSH1 < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) sh2idx   in Hcur.
      intuition.
      right;right;left; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) sh1idx   in Hcur.
      intuition.
      right;left;trivial. }
    destruct H0.
    destruct H0. 
     destruct H0 as (H0 &  H4).
    intuition.
    assert(Hnoteq : idxSH2 <> idxSH1).
    { subst.
      unfold sh2idx. unfold sh1idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    now contradict Hnoteq.
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh1idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh1idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh1idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (sh1idx + 1) tableSize ); intros.
    contradict H13.
    subst.
    unfold sh1idx. unfold sh2idx.
    unfold CIndex at 3.
    case_eq (lt_dec 6 tableSize); intros.
    unfold not; intros.
    inversion H14.
    unfold CIndex in H16.
    case_eq(lt_dec 4 tableSize); intros; rewrite H15 in *.
    inversion H16.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
    assert(Hnoteq : idxSH1 <> idxSH2).
    { subst.
      unfold sh1idx. unfold sh2idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh2idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh2idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh2idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (sh2idx + 1) tableSize ); intros.
    contradict H13.
    subst.
    unfold sh2idx. unfold sh1idx.
    unfold CIndex at 3.
    case_eq (lt_dec 4 tableSize); intros.
    unfold not; intros.
    inversion H14.
    unfold CIndex in H16.
    case_eq(lt_dec 6 tableSize); intros; rewrite H15 in *.
    inversion H16.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
    
      eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxSH2 < tableSize - 1 /\ idxPD < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) sh2idx   in Hcur.
      intuition.
      right;right;left ; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) PDidx   in Hcur.
      intuition.
      left;trivial. }
    destruct H0.
    destruct H0.
    destruct H0.  
    destruct H0 as (H0 &  H5).
    intuition.
    assert(Hnoteq : idxPD <> idxSH2).
    { subst.
      unfold PDidx. unfold sh2idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    now contradict Hnoteq.
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PDidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PDidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PDidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (PDidx + 1) tableSize ); intros.
    contradict H15.
    subst.
    unfold sh2idx. unfold PDidx.
    unfold CIndex at 3.
    case_eq (lt_dec 6 tableSize); intros.
    unfold not; intros.
    inversion H16.
    unfold CIndex in H18.
    case_eq(lt_dec 2 tableSize); intros; rewrite H17 in *.
    inversion H18.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
    assert(Hnoteq : idxPD <> idxSH2).
    { subst.
      unfold sh2idx. unfold PDidx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh2idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh2idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh2idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (sh2idx + 1) tableSize ); intros.
    contradict H15.
    subst.
    unfold PDidx. unfold sh2idx.
    unfold CIndex at 3.
    case_eq (lt_dec 2 tableSize); intros.
    unfold not; intros.
    inversion H16.
    unfold CIndex in H18.
    case_eq(lt_dec 6 tableSize); intros; rewrite H17 in *.
    inversion H18.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
          eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxSH2 < tableSize - 1 /\ idxPR < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) sh2idx   in Hcur.
      intuition.
      right;right;left ; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) PRidx   in Hcur.
      intuition.
      repeat right;trivial. }
    destruct H0.
    destruct H0.  
    destruct H0.
    destruct H0.
    
    destruct H0 as (H0 & _ & H6).
    intuition.
    assert(Hnoteq : idxPR <> idxSH2).
    { subst.
      unfold PRidx. unfold sh2idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    now contradict Hnoteq.
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (PRidx + 1) tableSize ); intros.
    contradict H17.
    subst.
    unfold sh2idx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 6 tableSize); intros.
    unfold not; intros Hfalse.
    inversion Hfalse.
    unfold CIndex in H19.
    case_eq(lt_dec 0 tableSize); intros; rewrite H18 in *.
    inversion H19.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
    assert(Hnoteq : idxPR <> idxSH2).
    { subst.
      unfold PRidx. unfold sh2idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh2idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh2idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh2idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (sh2idx + 1) tableSize ); intros.
    contradict H17.
    subst.
    unfold sh2idx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 0 tableSize); intros.
    unfold not; intros Hfalse.
    inversion Hfalse.
    unfold CIndex in H19.
    case_eq(lt_dec 6 tableSize); intros; rewrite H18 in *.
    inversion H19.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
    simpl; intros [].
    (** updatePartitionDescriptor : add the config list into the partition descriptor *)
    eapply WP.bindRev.
    eapply preAndPost.
    eapply preAndPost.
    eapply preAndPost.
    eapply preAndPost.    
    eapply WP.weaken.
    eapply conjPrePost.
    eapply updatePartitionDescriptorPropagatedProperties.
    intuition.
    eapply updatePartitionDescriptorNewProperty.
    simpl.
    intros.
    repeat rewrite and_assoc in H0.
    repeat rewrite and_assoc.
    destruct H0.
    destruct H1.
    split.
    eapply H0.
    instantiate(1:= ptRefChild).
    instantiate(1:= descChild).
    instantiate(1:=  idxRefChild).
    instantiate(1:=  idxPPR).
    instantiate(1:= idxSH3).
    instantiate(1:= idxSH2).
    instantiate(1:=  idxSH1).
    instantiate(1:=  idxPD).
    instantiate(1:=  idxPR).
       instantiate(1:=  nullv).
    instantiate(1:=  zero).
    unfold propagatedProperties in *.
    intuition.
    assert(Hget1 :forall idx : index,
                  StateLib.getIndexOfAddr descChild fstLevel = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild PDidx currentPart descChild s) by intuition.
    intuition.
    apply Hget1; trivial.
    assert(Hget1 :forall idx : index,
                  StateLib.getIndexOfAddr descChild fstLevel = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild PDidx currentPart descChild s) by intuition.
    intuition.
    assert(Hidx : StateLib.getIndexOfAddr descChild fstLevel = idxRefChild) by trivial.
    generalize (Hget1 idxRefChild Hidx);clear Hget1 ; intros (_ & Hhet1).
    subst. assumption.
    subst. assumption.
    unfold propagatedProperties in *.
    unfold consistency in *.
    intuition.
    subst.
    assert (Hpde : partitionDescriptorEntry s) by trivial.
    unfold  partitionDescriptorEntry in *.
    assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
    unfold currentPartitionInPartitionsList in *.
    intuition.
    apply Hpde with (currentPartition s)  sh3idx in Hcur.
    subst.
    intuition.
    do 3 right;left; trivial.
    unfold propagatedProperties in *.
    unfold consistency in *.
    intuition.
    subst.
    assert (Hpde : partitionDescriptorEntry s) by trivial.
    unfold  partitionDescriptorEntry in *.
    assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
    unfold currentPartitionInPartitionsList in *.
    intuition.
    apply Hpde with (currentPartition s) sh3idx  in Hcur.
    intuition.
    do 3 right; left; trivial.
    simpl.
    eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxSH2 < tableSize - 1 /\ idxSH3 < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) sh2idx   in Hcur.
      intuition.
      right;right;left; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) sh3idx   in Hcur.
      intuition.
      do 3 right;left;trivial. }
    destruct H0.
    destruct H0.  
    
    destruct H0 as (H0 &  H4).
    intuition.
    assert(Hnoteq : idxSH2 <> idxSH3).
    { subst.
      unfold sh2idx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    now contradict Hnoteq.
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh2idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh2idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh2idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (sh2idx + 1) tableSize ); intros.
    contradict H13.
    subst.
    unfold sh3idx. unfold sh2idx.
    unfold CIndex at 3.
    case_eq (lt_dec 8 tableSize); intros.
    unfold not; intros.
    inversion H14.
    unfold CIndex in H16.
    case_eq(lt_dec 6 tableSize); intros; rewrite H15 in *.
    inversion H16.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
    assert(Hnoteq : idxSH3 <> idxSH2).
    { subst.
      unfold sh3idx. unfold sh2idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh3idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh3idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh3idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (sh3idx + 1) tableSize ); intros.
    contradict H13.
    subst.
    unfold sh2idx. unfold sh3idx.
    unfold CIndex at 3.
    case_eq (lt_dec 6 tableSize); intros.
    unfold not; intros.
    inversion H14.
    unfold CIndex in H16.
    case_eq(lt_dec 8 tableSize); intros; rewrite H15 in *.
    inversion H16.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
    
      eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxSH1 < tableSize - 1 /\ idxSH3 < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) sh1idx   in Hcur.
      intuition.
      right;left ; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) sh3idx   in Hcur.
      intuition.
      do 3 right;left;trivial. }
    destruct H0.
    destruct H0.  
    destruct H0.
    
    destruct H0 as (H0 &  H5).
    intuition.
    assert(Hnoteq : idxSH1 <> idxSH3).
    { subst.
      unfold sh1idx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    now contradict Hnoteq.
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh1idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh1idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh1idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (sh1idx + 1) tableSize ); intros.
    contradict H15.
    subst.
    unfold sh1idx. unfold sh3idx.
    unfold CIndex at 3.
    case_eq (lt_dec 8 tableSize); intros.
    unfold not; intros.
    inversion H16.
    unfold CIndex in H18.
    case_eq(lt_dec 4 tableSize); intros; rewrite H17 in *.
    inversion H18.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
    assert(Hnoteq : idxSH3 <> idxSH1).
    { subst.
      unfold sh3idx. unfold sh1idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh3idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh3idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh3idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (sh3idx + 1) tableSize ); intros.
    contradict H15.
    subst.
    unfold sh1idx. unfold sh3idx.
    unfold CIndex at 3.
    case_eq (lt_dec 4 tableSize); intros.
    unfold not; intros.
    inversion H16.
    unfold CIndex in H18.
    case_eq(lt_dec 8 tableSize); intros; rewrite H17 in *.
    inversion H18.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
          eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxSH3 < tableSize - 1 /\ idxPD < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) sh3idx   in Hcur.
      intuition.
      do 3 right;left ; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) PDidx   in Hcur.
      intuition.
      left;trivial. }
    do 4 destruct H0.
    
    destruct H0 as (H0 &  H6).
    intuition.
    assert(Hnoteq : idxPD <> idxSH3).
    { subst.
      unfold PDidx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    now contradict Hnoteq.
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PDidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PDidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PDidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (PDidx + 1) tableSize ); intros.
    contradict H17.
    subst.
    unfold PDidx. unfold sh3idx.
    unfold CIndex at 3.
    case_eq (lt_dec 8 tableSize); intros.
    unfold not; intros Hfalse.
    inversion Hfalse.
    unfold CIndex in H19.
    case_eq(lt_dec 2 tableSize); intros; rewrite H18 in *.
    inversion H19.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
    assert(Hnoteq : idxSH3 <> idxPD).
    { subst.
      unfold sh3idx. unfold PDidx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh3idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh3idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh3idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (sh3idx + 1) tableSize ); intros.
    contradict H17.
    subst.
    unfold sh3idx. unfold PDidx.
    unfold CIndex at 3.
    case_eq (lt_dec 2 tableSize); intros.
    unfold not; intros Hfalse.
    inversion Hfalse.
    unfold CIndex in H19.
    case_eq(lt_dec 8 tableSize); intros; rewrite H18 in *.
    inversion H19.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
              eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxSH3 < tableSize - 1 /\ idxPR < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) sh3idx   in Hcur.
      intuition.
      do 3 right;left ; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) PRidx in Hcur.
      intuition.
      repeat right;trivial. }
    do 5 destruct H0.    
    destruct H0 as (H0 &  H7).
    intuition.
    assert(Hnoteq : idxPR <> idxSH3).
    { subst.
      unfold PRidx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    now contradict Hnoteq.
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (PRidx + 1) tableSize ); intros.
    contradict H19.
    subst.
    unfold PRidx. unfold sh3idx.
    unfold CIndex at 3.
    case_eq (lt_dec 8 tableSize); intros.
    unfold not; intros Hfalse.
    inversion Hfalse.
    unfold CIndex in H21.
    case_eq(lt_dec 0 tableSize); intros; rewrite H20 in *.
    inversion H21.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
    assert(Hnoteq : idxSH3 <> idxPR).
    { subst.
      unfold sh3idx. unfold PRidx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh3idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh3idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh3idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (sh3idx + 1) tableSize ); intros.
    contradict H19.
    subst.
    unfold sh3idx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 0 tableSize); intros.
    unfold not; intros Hfalse.
    inversion Hfalse.
    unfold CIndex in H21.
    case_eq(lt_dec 8 tableSize); intros; rewrite H20 in *.
    inversion H21.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
simpl.
intros [].
      (** updatePartitionDescriptor : add the config list into the partition descriptor *)
    eapply WP.bindRev.
    eapply preAndPost.
    eapply preAndPost.
    eapply preAndPost.
    eapply preAndPost.
    eapply preAndPost.    
    eapply WP.weaken.
    eapply conjPrePost.
    eapply updatePartitionDescriptorPropagatedProperties.
    intuition.
    eapply updatePartitionDescriptorNewProperty.
    simpl.
    intros.
    repeat rewrite and_assoc in H0.
    repeat rewrite and_assoc.
    destruct H0.
    destruct H1.
    split.
    eapply H0.
    instantiate(1:= ptRefChild).
    instantiate(1:= descChild).
    instantiate(1:=  idxRefChild).
    instantiate(1:=  idxPPR).
    instantiate(1:= idxSH3).
    instantiate(1:= idxSH2).
    instantiate(1:=  idxSH1).
    instantiate(1:=  idxPD).
    instantiate(1:=  idxPR).
       instantiate(1:=  nullv).
    instantiate(1:=  zero).
    unfold propagatedProperties in *.
    intuition.
    assert(Hget1 :forall idx : index,
                  StateLib.getIndexOfAddr descChild fstLevel = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild PDidx currentPart descChild s) by intuition.
    intuition.
    apply Hget1; trivial.
    assert(Hget1 :forall idx : index,
                  StateLib.getIndexOfAddr descChild fstLevel = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild PDidx currentPart descChild s) by intuition.
    intuition.
    assert(Hidx : StateLib.getIndexOfAddr descChild fstLevel = idxRefChild) by trivial.
    generalize (Hget1 idxRefChild Hidx);clear Hget1 ; intros (_ & Hhet1).
    subst. assumption.
    subst. assumption.
    unfold propagatedProperties in *.
    unfold consistency in *.
    intuition.
    subst.
    assert (Hpde : partitionDescriptorEntry s) by trivial.
    unfold  partitionDescriptorEntry in *.
    assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
    unfold currentPartitionInPartitionsList in *.
    intuition.
    apply Hpde with (currentPartition s)  PPRidx in Hcur.
    subst.
    intuition.
    do 4 right;left; trivial.
    unfold propagatedProperties in *.
    unfold consistency in *.
    intuition.
    subst.
    assert (Hpde : partitionDescriptorEntry s) by trivial.
    unfold  partitionDescriptorEntry in *.
    assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
    unfold currentPartitionInPartitionsList in *.
    intuition.
    apply Hpde with (currentPartition s) PPRidx  in Hcur.
    intuition.
    do 4 right; left; trivial.
    simpl.
    eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxPPR < tableSize - 1 /\ idxSH3 < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) PPRidx   in Hcur.
      intuition.
      do 4 right ;left; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) sh3idx   in Hcur.
      intuition.
      do 3 right;left;trivial. }
    do 2 destruct H0.    
    destruct H0 as (H0 &  H4).
    intuition.
    assert(Hnoteq : idxPPR <> idxSH3).
    { subst.
      unfold PPRidx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    now contradict Hnoteq.
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh3idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh3idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh3idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (sh3idx + 1) tableSize ); intros.
    contradict H13.
    subst.
    unfold sh3idx. unfold PPRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 10 tableSize); intros.
    unfold not; intros.
    inversion H14.
    unfold CIndex in H16.
    case_eq(lt_dec 8 tableSize); intros; rewrite H15 in *.
    inversion H16.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
    assert(Hnoteq : idxSH3 <> idxPPR).
    { subst.
      unfold sh3idx. unfold PPRidx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PPRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PPRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PPRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (PPRidx + 1) tableSize ); intros.
    contradict H13.
    subst.
    unfold PPRidx. unfold sh3idx.
    unfold CIndex at 3.
    case_eq (lt_dec 8 tableSize); intros.
    unfold not; intros.
    inversion H14.
    unfold CIndex in H16.
    case_eq(lt_dec 10 tableSize); intros; rewrite H15 in *.
    inversion H16.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega. 
      eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxPPR < tableSize - 1 /\ idxSH2 < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) PPRidx   in Hcur.
      intuition.
      do 4 right;left ; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) sh2idx   in Hcur.
      intuition.
      do 2 right;left;trivial. }
        do 3 destruct H0.    
    destruct H0 as (H0 &  H5).
    intuition.
    assert(Hnoteq : idxSH2 <> idxPPR).
    { subst.
      unfold sh1idx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    now contradict Hnoteq.
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh2idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh2idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh2idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (sh2idx + 1) tableSize ); intros.
    contradict H15.
    subst.
    unfold sh2idx. unfold PPRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 10 tableSize); intros.
    unfold not; intros.
    inversion H16.
    unfold CIndex in H18.
    case_eq(lt_dec 6 tableSize); intros; rewrite H17 in *.
    inversion H18.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
    assert(Hnoteq : idxPPR <> idxSH2).
    { subst.
      unfold PPRidx. unfold sh2idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PPRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PPRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PPRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (PPRidx + 1) tableSize ); intros.
    contradict H15.
    subst.
    unfold sh2idx. unfold PPRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 6 tableSize); intros.
    unfold not; intros.
    inversion H16.
    unfold CIndex in H18.
    case_eq(lt_dec 10 tableSize); intros; rewrite H17 in *.
    inversion H18.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
          eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxPPR < tableSize - 1 /\ idxSH1 < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) PPRidx   in Hcur.
      intuition.
      do 4 right;left ; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) sh1idx   in Hcur.
      intuition.
      right;left;trivial. }
        do 4 destruct H0.    
    destruct H0 as (H0 &  H6).

    intuition.
    assert(Hnoteq : idxSH1 <> idxPPR).
    { subst.
      unfold sh1idx. unfold PPRidx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    now contradict Hnoteq.
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh1idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh1idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh1idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (sh1idx + 1) tableSize ); intros.
    contradict H17.
    subst.
    unfold sh1idx. unfold PPRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 10 tableSize); intros.
    unfold not; intros Hfalse.
    inversion Hfalse.
    unfold CIndex in H19.
    case_eq(lt_dec 4 tableSize); intros; rewrite H18 in *.
    inversion H19.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
    assert(Hnoteq : idxPPR <> idxSH1).
    { subst.
      unfold PPRidx. unfold sh1idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PPRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PPRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PPRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (PPRidx + 1) tableSize ); intros.
    contradict H17.
    subst.
    unfold PPRidx. unfold sh1idx.
    unfold CIndex at 3.
    case_eq (lt_dec 4 tableSize); intros.
    unfold not; intros Hfalse.
    inversion Hfalse.
    unfold CIndex in H19.
    case_eq(lt_dec 10 tableSize); intros; rewrite H18 in *.
    inversion H19.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
              eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxPPR < tableSize - 1 /\ idxPD < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) PPRidx   in Hcur.
      intuition.
      do 4 right;left ; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) PDidx in Hcur.
      intuition.
      left;trivial. }
       do 5 destruct H0.    
    destruct H0 as (H0 &  H7).

    intuition.
    assert(Hnoteq : idxPD <> idxPPR).
    { subst.
      unfold PRidx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    now contradict Hnoteq.
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PDidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PDidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PDidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (PDidx + 1) tableSize ); intros.
    contradict H19.
    subst.
    unfold PDidx. unfold PPRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 10 tableSize); intros.
    unfold not; intros Hfalse.
    inversion Hfalse.
    unfold CIndex in H21.
    case_eq(lt_dec 2 tableSize); intros; rewrite H20 in *.
    inversion H21.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
    assert(Hnoteq : idxPPR <> idxPD).
    { subst.
      unfold PPRidx. unfold PDidx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PPRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PPRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PPRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (PPRidx + 1) tableSize ); intros.
    contradict H19.
    subst.
    unfold PPRidx. unfold PDidx.
    unfold CIndex at 3.
    case_eq (lt_dec 2 tableSize); intros.
    unfold not; intros Hfalse.
    inversion Hfalse.
    unfold CIndex in H21.
    case_eq(lt_dec 10 tableSize); intros; rewrite H20 in *.
    inversion H21.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
    eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxPPR < tableSize - 1 /\ idxPR < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) PPRidx   in Hcur.
      intuition.
      do 4 right;left ; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions multiplexer s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) PRidx in Hcur.
      intuition.
      repeat right;trivial. }
       do 6 destruct H0.    
    destruct H0 as (H0 &  H8).
    intuition.
    assert(Hnoteq : idxPR <> idxPPR).
    { subst.
      unfold PRidx. unfold PPRidx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    now contradict Hnoteq.
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (PRidx + 1) tableSize ); intros.
    contradict H21.
    subst.
    unfold PRidx. unfold PPRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 10 tableSize); intros.
    unfold not; intros Hfalse.
    inversion Hfalse.
    unfold CIndex in H23.
    case_eq(lt_dec 0 tableSize); intros; rewrite H22 in *.
    inversion H23.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
    assert(Hnoteq : idxPPR <> idxPR).
    { subst.
      unfold PPRidx. unfold PRidx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. apply tableSizeBigEnough. omega. }
    subst.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PPRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PPRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PPRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    omega.
    unfold CIndex.
    case_eq(lt_dec (PPRidx + 1) tableSize ); intros.
    contradict H21.
    subst.
    unfold PPRidx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 0 tableSize); intros.
    unfold not; intros Hfalse.
    inversion Hfalse.
    unfold CIndex in H23.
    case_eq(lt_dec 10 tableSize); intros; rewrite H22 in *.
    inversion H23.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega.
    omega.
    omega.
    simpl.
    intros []. 
(**  writeVirEntry **)
    eapply bindRev.
    eapply weaken.
    eapply WP.writeVirEntry.
    simpl; intros.
   repeat rewrite and_assoc  in H0.
   unfold propagatedProperties in *.
    destruct H0 as (H0 & Hnew).
    do 53 rewrite <- and_assoc in H0.
    destruct H0 as (H0 & Hsplit).
    destruct H0 as (H0 & Hfalse). 
    assert (Hpost := conj (conj H0 Hsplit)  Hnew).
    try repeat rewrite and_assoc in Hpost. 
    clear H0 Hfalse Hnew Hsplit.      
    pattern s in Hpost.
    match type of Hpost with 
    |?HT s => instantiate (1 := fun tt s => HT s /\ 
                                isEntryVA ptPDChildSh1 idxPDChild descChild s)
    end.
    simpl in *.
    split. 
    unfold propagatedProperties in *.
    assert(Hget : forall idx : index,
                  StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                  isVE ptPDChildSh1 idx s /\ 
                  getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s)
      by intuition.
    assert (Hve :isVE ptPDChildSh1 idxPDChild s).
    apply Hget.
    intuition.
    unfold isVE in Hve.
    case_eq( lookup ptPDChildSh1 idxPDChild (memory s) beqPage beqIndex);
    intros; rewrite H0 in *; try now contradict Hve.
    case_eq v ; intros;rewrite H1 in *; try now contradict Hve.
    assert(Hpartitions : getPartitions multiplexer
            {|
            currentPartition := currentPartition s;
            memory := add ptPDChildSh1 idxPDChild (VE {| pd := false; va := descChild |})
                        (memory s) beqPage beqIndex |} = 
                        getPartitions multiplexer
            s).
    apply getPartitionsAddDerivation with v0;trivial.
    unfold isPartitionFalse in *.
    intuition.
    do 3 rewrite <- and_assoc .
    split.
    (** partitionsIsolation **)
    do 2 rewrite and_assoc.
    split.
    assert (Hiso : partitionsIsolation s) by intuition.
    apply partitionsIsolationUpdtateSh1Structure with v0; trivial.
    assert(Hispart : isPartitionFalse ptPDChildSh1 idxPDChild s ) by intuition.
    unfold isPartitionFalse in *.
    assumption.
    (** kernelDataIsolation **)
    split.
    assert (Hkdi : kernelDataIsolation s) by intuition.
    apply kernelDataIsolationUpdtateSh1Structure with v0; trivial.
    assert(Hispart : isPartitionFalse ptPDChildSh1 idxPDChild s ) by intuition.
    unfold isPartitionFalse in *.
    assumption.
    (** VerticalSharing **)
    split.
    assert (Hvs : verticalSharing s) by intuition.
    apply verticalSharingUpdtateSh1Structure with v0; trivial.
    assert(Hispart : isPartitionFalse ptPDChildSh1 idxPDChild s ) by intuition.
    unfold isPartitionFalse in *.
    assumption.
    (** consistency **)
    assert (Hcons : consistency s ) by intuition.
    apply consistencyUpdtateSh1Structure with v0; trivial.
    unfold consistency in *. 
    assert(Hispart : isPartitionFalse ptPDChildSh1 idxPDChild s ) by intuition.
    unfold isPartitionFalse in *.
    assumption.
    (** Propagate properties **)
    { assert(Hconfig :forall partition,  getConfigPagesAux partition
            {|
            currentPartition := currentPartition s;
            memory := add ptPDChildSh1 idxPDChild (VE {| pd := false; va := descChild |}) 
                        (memory s) beqPage beqIndex |} = getConfigPagesAux partition s).
      { intros.
        apply getConfigPagesAuxAddDerivation with v0;trivial. }
     intuition try trivial. 
    + apply nextEntryIsPPAddDerivation with v0; trivial.
    + apply isPEAddDerivation with v0; trivial. 
      assert(Hi : forall idx : index,
                  StateLib.getIndexOfAddr descChild fstLevel = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild PDidx currentPart descChild s)
      by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxRefChild v0 isPE ; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isPE ptPDChild idx s /\ 
                    getTableAddrRoot ptPDChild PDidx currentPart pdChild s ) by
       intuition.
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxPDChild v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
                  StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                  isPE ptSh1Child idx s /\ 
                  getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s ) by
       intuition. 
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh1 v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
      isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s ) by
       intuition. 
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh2 v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
      StateLib.getIndexOfAddr list fstLevel = idx ->
      isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList PDidx currentPart list s ) by
       intuition. 
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxConfigPagesList v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0; trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxRefChild v0 isVE; trivial.
    + 
 (*   + assert (Hi : exists va : vaddr,
         isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
         beqVAddr defaultVAddr va = derivedRefChild ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with descChild
      pdChild   currentPart
      currentShadow1 sh1idx level isVE s ;trivial.
      right;left; trivial.
admit.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr pdChild fstLevel = idx ->
       isVE ptPDChildSh1 idx s /\
       getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxPDChild v0 isVE; trivial.
    + admit. 
    + assert(Hpartitions : getPartitions multiplexer
     {|
     currentPartition := currentPartition s;
     memory := add ptPDChildSh1 idxPDChild  (VE {| pd := false; va := descChild |}) 
                  (memory s) beqPage beqIndex |} = 
    getPartitions multiplexer s).
    { apply getPartitionsAddDerivation with v0; trivial.
      assert(Hispart : isPartitionFalse ptPDChildSh1 idxPDChild s ) by intuition.
      unfold isPartitionFalse in *.
      assumption. }
   assert(Hconfig :forall partition,  getConfigPagesAux partition
            {|
            currentPartition := currentPartition s;
            memory := add ptPDChildSh1 idxPDChild (VE {| pd := false; va := descChild |}) 
                        (memory s) beqPage beqIndex |} = getConfigPagesAux partition s).
    { intros.
      apply getConfigPagesAuxAddDerivation with v0;trivial. }                      
    intuition trivial.  *)
      assert (Hi : exists va : vaddr,
         isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
         beqVAddr defaultVAddr va = derivedRefChild ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with descChild
      pdChild   currentPart
      currentShadow1 sh1idx level isVE s ;trivial.
      right;left; trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr pdChild fstLevel = idx ->
       isVE ptPDChildSh1 idx s /\
       getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxPDChild v0 isVE; trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
       isVE ptSh1ChildFromSh1 idx s /\
       getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh1 v0 isVE; trivial.
    + assert (Hi : exists va : vaddr,
         isEntryVA ptSh1ChildFromSh1 idxSh1  va s /\ 
         beqVAddr defaultVAddr va = derivedSh1Child ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow1
      pdChild   currentPart
      currentShadow1 sh1idx level isVE s ;trivial.
      right;left; trivial.
      rewrite checkVAddrsEqualityWOOffsetPermut ;trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
       isVE childSh2 idx s /\
       getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh2 v0 isVE; trivial.
    + assert (Hi : exists va : vaddr,
         isEntryVA childSh2 idxSh2  va s /\ 
         beqVAddr defaultVAddr va = derivedSh2Child ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow2
      pdChild   currentPart
      currentShadow1 sh1idx level isVE s ;trivial.
      right;left; trivial.
      rewrite checkVAddrsEqualityWOOffsetPermut ;trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr list fstLevel = idx ->
       isVE childListSh1 idx s /\
       getTableAddrRoot childListSh1 sh1idx currentPart list s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxConfigPagesList v0 isVE; trivial.
    + assert (Hi : exists va : vaddr,
         isEntryVA  childListSh1 idxConfigPagesList  va s /\ 
         beqVAddr defaultVAddr va = derivedRefChildListSh1 ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with list
      pdChild   currentPart
      currentShadow1 sh1idx level isVE s ;trivial.
      right;left; trivial.
      rewrite checkVAddrsEqualityWOOffsetPermut ;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial. 
      right;trivial.
    +  assert (HisPart : isPartitionFalse ptSh1ChildFromSh1 idxSh1 s) by intuition.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag ptSh1ChildFromSh1 idxSh1
                (add ptPDChildSh1 idxPDChild (VE {| pd := false; va := descChild |})        
                (memory s) beqPage beqIndex) = StateLib.readPDflag ptSh1ChildFromSh1 
                idxSh1 (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow1 pdChild currentPart 
            currentShadow1 sh1idx level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
     rewrite Hreadflag;trivial.
    + assert (HisPart : isPartitionFalse childSh2 idxSh2 s) by trivial.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag childSh2 idxSh2
                (add ptPDChildSh1 idxPDChild (VE {| pd := false; va := descChild |})        
                (memory s) beqPage beqIndex) = StateLib.readPDflag childSh2 idxSh2
                (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow2 pdChild currentPart 
            currentShadow1 sh1idx level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
     rewrite Hreadflag;trivial.
(*     + apply entryUserFlagAddDerivation with v0;trivial. *)
    + assert (HisPart : isPartitionFalse childListSh1 idxConfigPagesList s) by trivial.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag childListSh1 idxConfigPagesList
                (add ptPDChildSh1 idxPDChild (VE {| pd := false; va := descChild |})        
                (memory s) beqPage beqIndex) = StateLib.readPDflag childListSh1
                 idxConfigPagesList
                (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with list pdChild currentPart 
            currentShadow1 sh1idx level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
     rewrite Hreadflag;trivial.
(*     + apply entryUserFlagAddDerivation with v0;trivial. *)
    +  assert (HisPart : isPartitionFalse ptRefChildFromSh1 idxRefChild s) by trivial.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag ptRefChildFromSh1 idxRefChild
                (add ptPDChildSh1 idxPDChild (VE {| pd := false; va := descChild |})        
                (memory s) beqPage beqIndex) = StateLib.readPDflag ptRefChildFromSh1
                 idxRefChild  (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with descChild pdChild currentPart 
            currentShadow1 sh1idx level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite Hreadflag;trivial.
    + apply isPartitionFalseAddDerivation.
(*     + apply entryUserFlagAddDerivation with v0;trivial.  *)
    + assert(Hi : forall idx : index, StateLib.readPhyEntry phySh2Child idx (memory s) = 
              Some defaultPage) by intuition.
      rewrite <- Hi with idx.
      apply readPhyEntryAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index, StateLib.readPhyEntry phySh1Child idx (memory s) = 
              Some defaultPage) by intuition.
      rewrite <- Hi with idx.
      apply readPhyEntryAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index, StateLib.readPhyEntry phyPDChild idx (memory s) = 
              Some defaultPage) by intuition.
      rewrite <- Hi with idx.
      apply readPhyEntryAddDerivation with v0;trivial.
    + assert(Hi : StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = 
              Some defaultPage)by intuition.
      rewrite <- Hi.
      apply readPhysicalAddDerivation with v0; trivial.
    + assert(Hi : forall idx : index,
      (idx = CIndex (tableSize - 1) -> False) ->
      Nat.Odd idx -> 
      StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) by intuition.
      rewrite <- Hi with idx;trivial.
      apply readVirtualAddDerivation with v0; trivial.
    + assert(Hi : forall idx : index,
      Nat.Even idx ->
      exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue)
      by trivial.
      assert (Heven : Nat.Even idx) by trivial.
      apply Hi in Heven.
      destruct Heven as (idxValue & Hidx).
      exists idxValue.
      rewrite <- Hidx.
      apply readIndexAddDerivation with v0; trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial. }
(** New property to propagate **)
    unfold isEntryVA.
    cbn.
    assert(Htrue : beqPairs (ptPDChildSh1, idxPDChild) (ptPDChildSh1, idxPDChild)
           beqPage beqIndex = true).
    { apply beqPairsTrue.
      split; trivial. }
    rewrite Htrue.
    cbn;trivial. 
 intros [].
 (**  writeVirEntry **)
    eapply bindRev.
    eapply weaken.
    eapply WP.writeVirEntry.
    simpl; intros.
    destruct H0 as (H0 & Hnew).
    do 55 rewrite <- and_assoc in H0.
    destruct H0 as (H0 & Hsplit).
    destruct H0 as (H0 & Hfalse). 
    assert (Hpost := conj (conj H0 Hsplit)  Hnew).
    try repeat rewrite and_assoc in Hpost. 
    clear H0 Hfalse Hnew Hsplit.      
    pattern s in Hpost.
    match type of Hpost with 
    |?HT s => instantiate (1 := fun tt s => HT s /\ 
                                isEntryVA ptSh1ChildFromSh1 idxSh1 descChild s)
    end.
    simpl in *.
    split. 
    unfold propagatedProperties in *.
    assert(Hget : forall idx : index,
                  StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                  isVE ptSh1ChildFromSh1 idx s /\ 
                  getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s)
      by intuition.
    assert (Hve :isVE ptSh1ChildFromSh1 idxSh1 s).
    apply Hget.
    intuition.
    unfold isVE in Hve.
    case_eq( lookup ptSh1ChildFromSh1 idxSh1 (memory s) beqPage beqIndex);
    intros; rewrite H0 in *; try now contradict Hve.
    case_eq v ; intros;rewrite H1 in *; try now contradict Hve.
    assert(Hpartitions : getPartitions multiplexer
            {|
            currentPartition := currentPartition s;
            memory := add ptSh1ChildFromSh1 idxSh1 (VE {| pd := false; va := descChild |})
                        (memory s) beqPage beqIndex |} = 
                        getPartitions multiplexer
            s).
    apply getPartitionsAddDerivation with v0;trivial.
    unfold isPartitionFalse in *.
    intuition.
    do 3 rewrite <- and_assoc .
    assert(Hispart : isPartitionFalse ptSh1ChildFromSh1 idxSh1 s ) by intuition.
    split.    
    (** partitionsIsolation **)
    do 2 rewrite and_assoc.
    split.
    assert (Hiso : partitionsIsolation s) by intuition.
    apply partitionsIsolationUpdtateSh1Structure with v0; trivial.
    (** kernelDataIsolation **)
    split.
    assert (Hkdi : kernelDataIsolation s) by intuition.
    apply kernelDataIsolationUpdtateSh1Structure with v0; trivial.
    (** VerticalSharing **)
    split.
    assert (Hvs : verticalSharing s) by intuition.
    apply verticalSharingUpdtateSh1Structure with v0; trivial.
    (** consistency **)
    assert (Hcons : consistency s ) by intuition.
    apply consistencyUpdtateSh1Structure with v0; trivial.
    (** Propagate properties **)
    { assert(Hconfig :forall partition,  getConfigPagesAux partition
            {|
            currentPartition := currentPartition s;
            memory := add ptSh1ChildFromSh1 idxSh1 (VE {| pd := false; va := descChild |}) 
                        (memory s) beqPage beqIndex |} = getConfigPagesAux partition s).
      { intros.
        apply getConfigPagesAuxAddDerivation with v0;trivial. }
     intuition try trivial. 
    + apply nextEntryIsPPAddDerivation with v0; trivial.
    + apply isPEAddDerivation with v0; trivial. 
      assert(Hi : forall idx : index,
                  StateLib.getIndexOfAddr descChild fstLevel = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild PDidx currentPart descChild s)
      by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxRefChild v0 isPE ; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isPE ptPDChild idx s /\ 
                    getTableAddrRoot ptPDChild PDidx currentPart pdChild s ) by
       intuition.
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxPDChild v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
                  StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                  isPE ptSh1Child idx s /\ 
                  getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s ) by
       intuition. 
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh1 v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
      isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s ) by
       intuition. 
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh2 v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
      StateLib.getIndexOfAddr list fstLevel = idx ->
      isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList PDidx currentPart list s ) by
       intuition. 
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxConfigPagesList v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0; trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxRefChild v0 isVE; trivial.
    + assert (Hi : exists va : vaddr,
         isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
         beqVAddr defaultVAddr va = derivedRefChild ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with descChild
      shadow1   currentPart
      currentShadow1 sh1idx level isVE s ;trivial.
      right;left; trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr pdChild fstLevel = idx ->
       isVE ptPDChildSh1 idx s /\
       getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxPDChild v0 isVE; trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
       isVE ptSh1ChildFromSh1 idx s /\
       getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh1 v0 isVE; trivial.
(*     + assert (Hi : exists va : vaddr,
         isEntryVA ptSh1ChildFromSh1 idxSh1  va s /\ 
         beqVAddr defaultVAddr va = derivedSh1Child ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow1
      pdChild   currentPart
      currentShadow1 sh1idx level isVE s ;trivial.
      right;left; trivial.
      rewrite checkVAddrsEqualityWOOffsetPermut ;trivial. *)
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
       isVE childSh2 idx s /\
       getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh2 v0 isVE; trivial.
    + assert (Hi : exists va : vaddr,
         isEntryVA childSh2 idxSh2  va s /\ 
         beqVAddr defaultVAddr va = derivedSh2Child ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow2
      shadow1   currentPart
      currentShadow1 sh1idx level isVE s ;trivial.
      right;left; trivial.
      rewrite checkVAddrsEqualityWOOffsetPermut ;trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr list fstLevel = idx ->
       isVE childListSh1 idx s /\
       getTableAddrRoot childListSh1 sh1idx currentPart list s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxConfigPagesList v0 isVE; trivial.
    + assert (Hi : exists va : vaddr,
         isEntryVA  childListSh1 idxConfigPagesList  va s /\ 
         beqVAddr defaultVAddr va = derivedRefChildListSh1 ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with list
      shadow1   currentPart
      currentShadow1 sh1idx level isVE s ;trivial.
      right;left; trivial.
      rewrite checkVAddrsEqualityWOOffsetPermut ;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial. 
      right;trivial.
    + apply isPartitionFalseAddDerivation.
(*     +  assert (HisPart : isPartitionFalse ptSh1ChildFromSh1 idxSh1 s) by intuition.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag ptSh1ChildFromSh1 idxSh1
                (add ptPDChildSh1 idxPDChild (VE {| pd := false; va := descChild |})        
                (memory s) beqPage beqIndex) = StateLib.readPDflag ptSh1ChildFromSh1 
                idxSh1 (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow1 pdChild currentPart 
            currentShadow1 sh1idx level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
     rewrite Hreadflag;trivial. *)
    + assert (HisPart : isPartitionFalse childSh2 idxSh2 s) by trivial.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag childSh2 idxSh2
                (add ptSh1ChildFromSh1 idxSh1 (VE {| pd := false; va := descChild |})        
                (memory s) beqPage beqIndex) = StateLib.readPDflag childSh2 idxSh2
                (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow2 shadow1 currentPart 
            currentShadow1 sh1idx level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
     rewrite Hreadflag;trivial.
(*     + apply entryUserFlagAddDerivation with v0;trivial. *)
    + assert (HisPart : isPartitionFalse childListSh1 idxConfigPagesList s) by trivial.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag childListSh1 idxConfigPagesList
                (add ptSh1ChildFromSh1 idxSh1 (VE {| pd := false; va := descChild |})        
                (memory s) beqPage beqIndex) = StateLib.readPDflag childListSh1
                 idxConfigPagesList
                (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with list shadow1 currentPart 
            currentShadow1 sh1idx level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
     rewrite Hreadflag;trivial.
(*     + apply entryUserFlagAddDerivation with v0;trivial. *)
    +  assert (HisPart : isPartitionFalse ptRefChildFromSh1 idxRefChild s) by trivial.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag ptRefChildFromSh1 idxRefChild
                (add ptSh1ChildFromSh1 idxSh1(VE {| pd := false; va := descChild |})        
                (memory s) beqPage beqIndex) = StateLib.readPDflag ptRefChildFromSh1
                 idxRefChild  (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with descChild shadow1 currentPart 
            currentShadow1 sh1idx level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite Hreadflag;trivial.
   +  assert (HisPart : isPartitionFalse ptPDChildSh1 idxPDChild s) by intuition.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag ptPDChildSh1 idxPDChild
                (add ptSh1ChildFromSh1 idxSh1 (VE {| pd := false; va := descChild |})        
                (memory s) beqPage beqIndex) = StateLib.readPDflag ptPDChildSh1 idxPDChild
                 (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with pdChild shadow1 currentPart 
            currentShadow1 sh1idx level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite Hreadflag;trivial.
(*     + apply entryUserFlagAddDerivation with v0;trivial.  *)
    + assert(Hi : forall idx : index, StateLib.readPhyEntry phySh2Child idx (memory s) = 
              Some defaultPage) by intuition.
      rewrite <- Hi with idx.
      apply readPhyEntryAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index, StateLib.readPhyEntry phySh1Child idx (memory s) = 
              Some defaultPage) by intuition.
      rewrite <- Hi with idx.
      apply readPhyEntryAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index, StateLib.readPhyEntry phyPDChild idx (memory s) = 
              Some defaultPage) by intuition.
      rewrite <- Hi with idx.
      apply readPhyEntryAddDerivation with v0;trivial.
    + assert(Hi : StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = 
              Some defaultPage)by intuition.
      rewrite <- Hi.
      apply readPhysicalAddDerivation with v0; trivial.
    + assert(Hi : forall idx : index,
      (idx = CIndex (tableSize - 1) -> False) ->
      Nat.Odd idx -> 
      StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) by intuition.
      rewrite <- Hi with idx;trivial.
      apply readVirtualAddDerivation with v0; trivial.
    + assert(Hi : forall idx : index,
      Nat.Even idx ->
      exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue)
      by trivial.
      assert (Heven : Nat.Even idx) by trivial.
      apply Hi in Heven.
      destruct Heven as (idxValue & Hidx).
      exists idxValue.
      rewrite <- Hidx.
      apply readIndexAddDerivation with v0; trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + Lemma isEntryVASameValue table1 table2 idx1 idx2 vaValue  s : 
     
     isEntryVA table1 idx1 vaValue s ->
      isEntryVA table1 idx1 vaValue
      {| currentPartition := currentPartition s;
         memory := add table2 idx2 (VE {| pd := false; va := vaValue |}) 
                  (memory s) beqPage beqIndex |}.
      Proof.
    
      unfold isEntryVA.
      cbn.
      case_eq(beqPairs (table2, idx2) (table1, idx1) beqPage beqIndex);
      intros * Hpairs;simpl;trivial.
      assert(lookup table1 idx1 (removeDup table2 idx2 (memory s) beqPage beqIndex) 
      beqPage beqIndex = lookup table1 idx1 (memory s) beqPage beqIndex ).
      apply beqPairsFalse in Hpairs.
      apply removeDupIdentity;intuition.
      rewrite H.
      trivial. Qed.
      apply isEntryVASameValue;trivial. }
      
(** New property to propagate **)
    unfold isEntryVA.
    cbn.
    assert(Htrue : beqPairs (ptSh1ChildFromSh1, idxSh1) (ptSh1ChildFromSh1, idxSh1) 
    beqPage beqIndex = true).
    { apply beqPairsTrue.
      split; trivial. }
    rewrite Htrue.
    cbn;trivial. 
 intros [].
 (**  writeVirEntry **)
    eapply bindRev.
    eapply weaken.
    eapply WP.writeVirEntry.
    simpl; intros.
    destruct H0 as (H0 & Hnew).
    do 57 rewrite <- and_assoc in H0.
    destruct H0 as (H0 & Hsplit).
    destruct H0 as (H0 & Hfalse). 
    assert (Hpost := conj (conj H0 Hsplit)  Hnew).
    try repeat rewrite and_assoc in Hpost. 
    clear H0 Hfalse Hnew Hsplit.      
    pattern s in Hpost.
    match type of Hpost with 
    |?HT s => instantiate (1 := fun tt s => HT s /\ 
                                isEntryVA childSh2 idxSh2 descChild s)
    end.
    simpl in *.
    split. 
    unfold propagatedProperties in *.
    assert(Hget : forall idx : index,
                  StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                  isVE childSh2 idx s /\ 
                  getTableAddrRoot childSh2 sh1idx currentPart shadow2 s)
      by intuition.
    assert (Hve :isVE childSh2 idxSh2  s).
    apply Hget.
    intuition.
    unfold isVE in Hve.
    case_eq( lookup childSh2 idxSh2  (memory s) beqPage beqIndex);
    intros; rewrite H0 in *; try now contradict Hve.
    case_eq v ; intros;rewrite H1 in *; try now contradict Hve.
    assert(Hpartitions : getPartitions multiplexer
            {|
            currentPartition := currentPartition s;
            memory := add childSh2 idxSh2  (VE {| pd := false; va := descChild |})
                        (memory s) beqPage beqIndex |} = 
                        getPartitions multiplexer
            s).
    apply getPartitionsAddDerivation with v0;trivial.
    unfold isPartitionFalse in *.
    intuition.
    do 3 rewrite <- and_assoc .
    assert(Hispart : isPartitionFalse childSh2 idxSh2  s ) by intuition.
    split.    
    (** partitionsIsolation **)
    do 2 rewrite and_assoc.
    split.
    assert (Hiso : partitionsIsolation s) by intuition.
    apply partitionsIsolationUpdtateSh1Structure with v0; trivial.
    (** kernelDataIsolation **)
    split.
    assert (Hkdi : kernelDataIsolation s) by intuition.
    apply kernelDataIsolationUpdtateSh1Structure with v0; trivial.
    (** VerticalSharing **)
    split.
    assert (Hvs : verticalSharing s) by intuition.
    apply verticalSharingUpdtateSh1Structure with v0; trivial.
    (** consistency **)
    assert (Hcons : consistency s ) by intuition.
    apply consistencyUpdtateSh1Structure with v0; trivial.
    (** Propagate properties **)
    { assert(Hconfig :forall partition,  getConfigPagesAux partition
            {|
            currentPartition := currentPartition s;
            memory := add childSh2 idxSh2  (VE {| pd := false; va := descChild |}) 
                        (memory s) beqPage beqIndex |} = getConfigPagesAux partition s).
      { intros.
        apply getConfigPagesAuxAddDerivation with v0;trivial. }
     intuition try trivial. 
    + apply nextEntryIsPPAddDerivation with v0; trivial.
    + apply isPEAddDerivation with v0; trivial. 
      assert(Hi : forall idx : index,
                  StateLib.getIndexOfAddr descChild fstLevel = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild PDidx currentPart descChild s)
      by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxRefChild v0 isPE ; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isPE ptPDChild idx s /\ 
                    getTableAddrRoot ptPDChild PDidx currentPart pdChild s ) by
       intuition.
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxPDChild v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
                  StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                  isPE ptSh1Child idx s /\ 
                  getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s ) by
       intuition. 
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh1 v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
      isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s ) by
       intuition. 
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh2 v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
      StateLib.getIndexOfAddr list fstLevel = idx ->
      isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList PDidx currentPart list s ) by
       intuition. 
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxConfigPagesList v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0; trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxRefChild v0 isVE; trivial.
    + assert (Hi : exists va : vaddr,
         isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
         beqVAddr defaultVAddr va = derivedRefChild ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with descChild
      shadow2   currentPart
      currentShadow1 sh1idx level isVE s ;trivial.
      right;left; trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr pdChild fstLevel = idx ->
       isVE ptPDChildSh1 idx s /\
       getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxPDChild v0 isVE; trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
       isVE ptSh1ChildFromSh1 idx s /\
       getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh1 v0 isVE; trivial.
(*     + assert (Hi : exists va : vaddr,
         isEntryVA ptSh1ChildFromSh1 idxSh1  va s /\ 
         beqVAddr defaultVAddr va = derivedSh1Child ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow1
      pdChild   currentPart
      currentShadow1 sh1idx level isVE s ;trivial.
      right;left; trivial.
      rewrite checkVAddrsEqualityWOOffsetPermut ;trivial. *)
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
       isVE childSh2 idx s /\
       getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh2 v0 isVE; trivial.
(*     + assert (Hi : exists va : vaddr,
         isEntryVA childSh2 idxSh2  va s /\ 
         beqVAddr defaultVAddr va = derivedSh2Child ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow2
      shadow1   currentPart
      currentShadow1 sh1idx level isVE s ;trivial.
      right;left; trivial.
      rewrite checkVAddrsEqualityWOOffsetPermut ;trivial. *)
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr list fstLevel = idx ->
       isVE childListSh1 idx s /\
       getTableAddrRoot childListSh1 sh1idx currentPart list s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxConfigPagesList v0 isVE; trivial.
    + assert (Hi : exists va : vaddr,
         isEntryVA  childListSh1 idxConfigPagesList  va s /\ 
         beqVAddr defaultVAddr va = derivedRefChildListSh1 ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with list
      shadow2   currentPart
      currentShadow1 sh1idx level isVE s ;trivial.
      right;left; trivial.
      rewrite checkVAddrsEqualityWOOffsetPermut ;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial. 
      right;trivial. 
   +  assert (HisPart : isPartitionFalse ptSh1ChildFromSh1 idxSh1 s) by intuition.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag ptSh1ChildFromSh1 idxSh1
                (add childSh2 idxSh2 (VE {| pd := false; va := descChild |})        
                (memory s) beqPage beqIndex) = StateLib.readPDflag ptSh1ChildFromSh1 
                idxSh1 (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow1 shadow2 currentPart 
            currentShadow1 sh1idx level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite Hreadflag;trivial.
    + apply isPartitionFalseAddDerivation. 
(*     + assert (HisPart : isPartitionFalse childSh2 idxSh2 s) by trivial.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag childSh2 idxSh2
                (add ptSh1ChildFromSh1 idxSh1 (VE {| pd := false; va := descChild |})        
                (memory s) beqPage beqIndex) = StateLib.readPDflag childSh2 idxSh2
                (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow2 shadow1 currentPart 
            currentShadow1 sh1idx level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
     rewrite Hreadflag;trivial. *)
(*     + apply entryUserFlagAddDerivation with v0;trivial. *)
    + assert (HisPart : isPartitionFalse childListSh1 idxConfigPagesList s) by trivial.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag childListSh1 idxConfigPagesList
                (add childSh2 idxSh2 (VE {| pd := false; va := descChild |})        
                (memory s) beqPage beqIndex) = StateLib.readPDflag childListSh1
                 idxConfigPagesList
                (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with list shadow2 currentPart 
            currentShadow1 sh1idx level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
     rewrite Hreadflag;trivial.
(*     + apply entryUserFlagAddDerivation with v0;trivial. *)
    +  assert (HisPart : isPartitionFalse ptRefChildFromSh1 idxRefChild s) by trivial.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag ptRefChildFromSh1 idxRefChild
                (add childSh2 idxSh2 (VE {| pd := false; va := descChild |})        
                (memory s) beqPage beqIndex) = StateLib.readPDflag ptRefChildFromSh1
                 idxRefChild  (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with descChild shadow2 currentPart 
            currentShadow1 sh1idx level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite Hreadflag;trivial.
   +  assert (HisPart : isPartitionFalse ptPDChildSh1 idxPDChild s) by intuition.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag ptPDChildSh1 idxPDChild
                (add childSh2 idxSh2 (VE {| pd := false; va := descChild |})        
                (memory s) beqPage beqIndex) = StateLib.readPDflag ptPDChildSh1 idxPDChild
                 (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with pdChild shadow2 currentPart 
            currentShadow1 sh1idx level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite Hreadflag;trivial.
(*     + apply entryUserFlagAddDerivation with v0;trivial.  *)
    + assert(Hi : forall idx : index, StateLib.readPhyEntry phySh2Child idx (memory s) = 
              Some defaultPage) by intuition.
      rewrite <- Hi with idx.
      apply readPhyEntryAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index, StateLib.readPhyEntry phySh1Child idx (memory s) = 
              Some defaultPage) by intuition.
      rewrite <- Hi with idx.
      apply readPhyEntryAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index, StateLib.readPhyEntry phyPDChild idx (memory s) = 
              Some defaultPage) by intuition.
      rewrite <- Hi with idx.
      apply readPhyEntryAddDerivation with v0;trivial.
    + assert(Hi : StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = 
              Some defaultPage)by intuition.
      rewrite <- Hi.
      apply readPhysicalAddDerivation with v0; trivial.
    + assert(Hi : forall idx : index,
      (idx = CIndex (tableSize - 1) -> False) ->
      Nat.Odd idx -> 
      StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) by intuition.
      rewrite <- Hi with idx;trivial.
      apply readVirtualAddDerivation with v0; trivial.
    + assert(Hi : forall idx : index,
      Nat.Even idx ->
      exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue)
      by trivial.
      assert (Heven : Nat.Even idx) by trivial.
      apply Hi in Heven.
      destruct Heven as (idxValue & Hidx).
      exists idxValue.
      rewrite <- Hidx.
      apply readIndexAddDerivation with v0; trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isEntryVASameValue;trivial.
    + apply isEntryVASameValue;trivial.
    }
      
(** New property to propagate **)
    unfold isEntryVA.
    cbn.
    assert(Htrue : beqPairs (childSh2, idxSh2) (childSh2, idxSh2) beqPage beqIndex
 = true).
    { apply beqPairsTrue.
      split; trivial. }
    rewrite Htrue.
    cbn;trivial. 
 intros [].
 (**  writeVirEntry **)
    eapply bindRev.
    eapply weaken.
    eapply WP.writeVirEntry.
    simpl; intros.
    destruct H0 as (H0 & Hnew).
    do 59 rewrite <- and_assoc in H0.
    destruct H0 as (H0 & Hsplit).
    destruct H0 as (H0 & Hfalse). 
    assert (Hpost := conj (conj H0 Hsplit)  Hnew).
    try repeat rewrite and_assoc in Hpost. 
    clear H0 Hfalse Hnew Hsplit.      
    pattern s in Hpost.
    match type of Hpost with 
    |?HT s => instantiate (1 := fun tt s => HT s /\ 
                                isEntryVA  childListSh1 idxConfigPagesList descChild s)
    end.
    simpl in *.
    split. 
    unfold propagatedProperties in *.
    assert(Hget : forall idx : index,
                  StateLib.getIndexOfAddr list fstLevel = idx ->
                  isVE childListSh1 idx s /\ 
                  getTableAddrRoot childListSh1 sh1idx currentPart list s)
      by intuition.
    assert (Hve :isVE childListSh1 idxConfigPagesList  s).
    apply Hget.
    intuition.
    unfold isVE in Hve.
    case_eq( lookup childListSh1 idxConfigPagesList  (memory s) beqPage beqIndex);
    intros; rewrite H0 in *; try now contradict Hve.
    case_eq v ; intros;rewrite H1 in *; try now contradict Hve.
    assert(Hpartitions : getPartitions multiplexer
            {|
            currentPartition := currentPartition s;
            memory := add childListSh1 idxConfigPagesList  (VE {| pd := false; va := descChild |})
                        (memory s) beqPage beqIndex |} = 
                        getPartitions multiplexer
            s).
    apply getPartitionsAddDerivation with v0;trivial.
    unfold isPartitionFalse in *.
    intuition.
    do 3 rewrite <- and_assoc .
    assert(Hispart : isPartitionFalse childListSh1 idxConfigPagesList  s ) by intuition.
    split.    
    (** partitionsIsolation **)
    do 2 rewrite and_assoc.
    split.
    assert (Hiso : partitionsIsolation s) by intuition.
    apply partitionsIsolationUpdtateSh1Structure with v0; trivial.
    (** kernelDataIsolation **)
    split.
    assert (Hkdi : kernelDataIsolation s) by intuition.
    apply kernelDataIsolationUpdtateSh1Structure with v0; trivial.
    (** VerticalSharing **)
    split.
    assert (Hvs : verticalSharing s) by intuition.
    apply verticalSharingUpdtateSh1Structure with v0; trivial.
    (** consistency **)
    assert (Hcons : consistency s ) by intuition.
    apply consistencyUpdtateSh1Structure with v0; trivial.
    (** Propagate properties **)
    { assert(Hconfig :forall partition,  getConfigPagesAux partition
            {|
            currentPartition := currentPartition s;
            memory := add childListSh1 idxConfigPagesList (VE {| pd := false; va := descChild |}) 
                        (memory s) beqPage beqIndex |} = getConfigPagesAux partition s).
      { intros.
        apply getConfigPagesAuxAddDerivation with v0;trivial. }
     intuition try trivial. 
    + apply nextEntryIsPPAddDerivation with v0; trivial.
    + apply isPEAddDerivation with v0; trivial. 
      assert(Hi : forall idx : index,
                  StateLib.getIndexOfAddr descChild fstLevel = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild PDidx currentPart descChild s)
      by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxRefChild v0 isPE ; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isPE ptPDChild idx s /\ 
                    getTableAddrRoot ptPDChild PDidx currentPart pdChild s ) by
       intuition.
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxPDChild v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
                  StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                  isPE ptSh1Child idx s /\ 
                  getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s ) by
       intuition. 
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh1 v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
      isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s ) by
       intuition. 
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh2 v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
      StateLib.getIndexOfAddr list fstLevel = idx ->
      isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList PDidx currentPart list s ) by
       intuition. 
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxConfigPagesList v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0; trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxRefChild v0 isVE; trivial.
    + assert (Hi : exists va : vaddr,
         isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
         beqVAddr defaultVAddr va = derivedRefChild ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with descChild
      list   currentPart
      currentShadow1 sh1idx level isVE s ;trivial.
      right;left; trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr pdChild fstLevel = idx ->
       isVE ptPDChildSh1 idx s /\
       getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxPDChild v0 isVE; trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
       isVE ptSh1ChildFromSh1 idx s /\
       getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh1 v0 isVE; trivial.
(*     + assert (Hi : exists va : vaddr,
         isEntryVA ptSh1ChildFromSh1 idxSh1  va s /\ 
         beqVAddr defaultVAddr va = derivedSh1Child ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow1
      pdChild   currentPart
      currentShadow1 sh1idx level isVE s ;trivial.
      right;left; trivial.
      rewrite checkVAddrsEqualityWOOffsetPermut ;trivial. *)
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
       isVE childSh2 idx s /\
       getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh2 v0 isVE; trivial.
(*     + assert (Hi : exists va : vaddr,
         isEntryVA childSh2 idxSh2  va s /\ 
         beqVAddr defaultVAddr va = derivedSh2Child ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow2
      shadow1   currentPart
      currentShadow1 sh1idx level isVE s ;trivial.
      right;left; trivial.
      rewrite checkVAddrsEqualityWOOffsetPermut ;trivial. *)
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr list fstLevel = idx ->
       isVE childListSh1 idx s /\
       getTableAddrRoot childListSh1 sh1idx currentPart list s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxConfigPagesList v0 isVE; trivial.
(*     + assert (Hi : exists va : vaddr,
         isEntryVA  childListSh1 idxConfigPagesList  va s /\ 
         beqVAddr defaultVAddr va = derivedRefChildListSh1 ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with list
      shadow2   currentPart
      currentShadow1 sh1idx level isVE s ;trivial.
      right;left; trivial.
      rewrite checkVAddrsEqualityWOOffsetPermut ;trivial. *)
    + apply isEntryPageAddDerivation with v0; trivial.    
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial. 
      right;trivial. 
   +  assert (HisPart : isPartitionFalse ptSh1ChildFromSh1 idxSh1 s) by intuition.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag ptSh1ChildFromSh1 idxSh1
                (add childListSh1 idxConfigPagesList (VE {| pd := false; va := descChild |})        
                (memory s) beqPage beqIndex) = StateLib.readPDflag ptSh1ChildFromSh1 
                idxSh1 (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow1 list currentPart 
            currentShadow1 sh1idx level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite Hreadflag;trivial.
   + assert (HisPart : isPartitionFalse childSh2 idxSh2 s) by trivial.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag childSh2 idxSh2
                (add childListSh1 idxConfigPagesList (VE {| pd := false; va := descChild |})        
                (memory s) beqPage beqIndex) = StateLib.readPDflag childSh2 idxSh2
                (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow2 list currentPart 
            currentShadow1 sh1idx level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite Hreadflag;trivial. 
(*     + apply entryUserFlagAddDerivation with v0;trivial. *)
    + apply isPartitionFalseAddDerivation.
    (* assert (HisPart : isPartitionFalse childListSh1 idxConfigPagesList s) by trivial.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag childListSh1 idxConfigPagesList
                (add childSh2 idxSh2 (VE {| pd := false; va := descChild |})        
                (memory s) beqPage beqIndex) = StateLib.readPDflag childListSh1
                 idxConfigPagesList
                (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with list shadow2 currentPart 
            currentShadow1 sh1idx level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
     rewrite Hreadflag;trivial.*)
(*     + apply entryUserFlagAddDerivation with v0;trivial. *)
    +  assert (HisPart : isPartitionFalse ptRefChildFromSh1 idxRefChild s) by trivial.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag ptRefChildFromSh1 idxRefChild
                (add childListSh1 idxConfigPagesList (VE {| pd := false; va := descChild |})        
                (memory s) beqPage beqIndex) = StateLib.readPDflag ptRefChildFromSh1
                 idxRefChild  (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with descChild list currentPart 
            currentShadow1 sh1idx level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite Hreadflag;trivial.
   +  assert (HisPart : isPartitionFalse ptPDChildSh1 idxPDChild s) by intuition.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag ptPDChildSh1 idxPDChild
                (add childListSh1 idxConfigPagesList (VE {| pd := false; va := descChild |})        
                (memory s) beqPage beqIndex) = StateLib.readPDflag ptPDChildSh1 idxPDChild
                 (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with pdChild list currentPart 
            currentShadow1 sh1idx level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite Hreadflag;trivial.
(*     + apply entryUserFlagAddDerivation with v0;trivial.  *)
    + assert(Hi : forall idx : index, StateLib.readPhyEntry phySh2Child idx (memory s) = 
              Some defaultPage) by intuition.
      rewrite <- Hi with idx.
      apply readPhyEntryAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index, StateLib.readPhyEntry phySh1Child idx (memory s) = 
              Some defaultPage) by intuition.
      rewrite <- Hi with idx.
      apply readPhyEntryAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index, StateLib.readPhyEntry phyPDChild idx (memory s) = 
              Some defaultPage) by intuition.
      rewrite <- Hi with idx.
      apply readPhyEntryAddDerivation with v0;trivial.
    + assert(Hi : StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = 
              Some defaultPage)by intuition.
      rewrite <- Hi.
      apply readPhysicalAddDerivation with v0; trivial.
    + assert(Hi : forall idx : index,
      (idx = CIndex (tableSize - 1) -> False) ->
      Nat.Odd idx -> 
      StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) by intuition.
      rewrite <- Hi with idx;trivial.
      apply readVirtualAddDerivation with v0; trivial.
    + assert(Hi : forall idx : index,
      Nat.Even idx ->
      exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue)
      by trivial.
      assert (Heven : Nat.Even idx) by trivial.
      apply Hi in Heven.
      destruct Heven as (idxValue & Hidx).
      exists idxValue.
      rewrite <- Hidx.
      apply readIndexAddDerivation with v0; trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isEntryVASameValue;trivial.
    + apply isEntryVASameValue;trivial.
    + apply isEntryVASameValue;trivial.
    }
      
(** New property to propagate **)
    unfold isEntryVA.
    cbn.
    assert(Htrue : beqPairs (childListSh1, idxConfigPagesList) (childListSh1, idxConfigPagesList)
     beqPage beqIndex
 = true).
    { apply beqPairsTrue.
      split; trivial. }
    rewrite Htrue.
    cbn;trivial. 
 intros [].
(**  writeVirEntry **)   
    admit. (** TODO : To be finished *)
 - intros HNotlegit. 
   eapply WP.weaken. eapply WP.ret .
   simpl. intuition.
      } 
      intros. eapply WP.weaken. eapply WP.ret .
      simpl. intuition.
      intros. eapply WP.weaken. eapply WP.ret .
      simpl. intuition.
Admitted.
