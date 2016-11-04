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
    This file contains the invariant of [writeAccessibleRec] *)
Require Import Core.Internal Isolation Consistency WeakestPreconditions StateLib
Model.Hardware Model.ADT Invariants  DependentTypeLemmas
GetTableAddr Model.MAL Model.Lib Lib InternalLemmas WriteAccessible
PropagatedProperties.
Require Import Coq.Logic.ProofIrrelevance Omega List.
Import List.ListNotations.

Lemma WriteAccessibleRec accessibleChild accessibleSh1 accessibleSh2 accessibleList 
descParent va  pt (phypage : page) idxvaparent pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
  ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
 presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
 idxConfigPagesList presentConfigPagesList 
 currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
 ptSh1ChildFromSh1 derivedSh1Child childSh2
 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild: 
{{  fun s : state =>
 propagatedProperties  accessibleChild accessibleSh1 accessibleSh2 accessibleList 
 pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
  ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
 presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
 idxConfigPagesList presentConfigPagesList 
 currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
 ptSh1ChildFromSh1 derivedSh1Child childSh2
 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild s /\
 
isAncestor  currentPart descParent s /\
 ( In descParent (getPartitions MALInternal.multiplexer s)  /\
     (defaultPage =? phypage) = false /\
    (forall idx : index,
StateLib.getIndexOfAddr va fstLevel = idx ->
isPE pt idx s /\ getTableAddrRoot pt PDidx descParent va s) /\
(defaultPage =? pt) = false /\
StateLib.getIndexOfAddr va fstLevel = idxvaparent /\
entryPresentFlag pt idxvaparent true s /\
entryUserFlag pt idxvaparent false s /\
    isEntryPage pt idxvaparent phypage s /\
    isAccessibleMappedPageInParent descParent va phypage s = true )
    }} 
  Internal.writeAccessibleRec nbPage va descParent false {{
    fun _ s  =>
     propagatedProperties  accessibleChild accessibleSh1 accessibleSh2 accessibleList 
 pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
  ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
 presentSh1 ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList 
 idxConfigPagesList presentConfigPagesList 
 currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
 ptSh1ChildFromSh1 derivedSh1Child childSh2
 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild s  
     }}.
Proof.
revert va descParent  pt phypage idxvaparent .
induction nbPage.
intros;simpl.
eapply weaken.
eapply WP.ret. simpl. intuition.
intros.
simpl.
eapply bindRev.
(** getMultiplexer **)
eapply weaken.
eapply Invariants.getMultiplexer.
intros; simpl.
pattern s in H.
eapply H.
simpl. 
intros multiplexer.
eapply bindRev.
(** Page.eqb **)
eapply weaken.
eapply Invariants.Page.eqb.
simpl.
intros.
pattern s in H.
eapply H.
simpl.
intros isMultiplexer.
case_eq isMultiplexer.
(** case_eq isMultiplexer true **)
+ intros isMultiplexerT.
  (** ret **)
  eapply weaken.
  eapply WP.ret.
  simpl. 
  intros.
  intuition.
(** case_eq isMultiplexer false **)
+ intros isMultiplexerF.
  eapply bindRev.
  (** getSndShadow **)
  eapply weaken.
  eapply Invariants.getSndShadow.
  simpl; intros.
  split.
  pattern s in H.
  eapply H.
  unfold propagatedProperties in H.
  unfold consistency in H;intuition.
 (** In descParent (getPartitions MALInternal.multiplexer s)**)
  intros sh2; simpl.
  eapply bindRev.
  (** getNbLevel **)
  eapply weaken.
  eapply Invariants.getNbLevel.
  intros; simpl.
  pattern s in H.
  eapply H.
  intros L; simpl. 
  (** getIndexOfAddr **) 
  eapply bindRev.
  eapply weaken.
  eapply Invariants.getIndexOfAddr.
  simpl; intros.
  pattern s in H.
  eapply H.
  intros lastIndex.
  simpl.
  (** getTableAddr **)
  eapply bindRev.
  eapply weaken.
  eapply GetTableAddr.getTableAddr.
  simpl. 
  intros.
  split.
  pattern s in H.
  eapply H.
  instantiate (1 :=  sh2idx).
  unfold propagatedProperties in H.
  split.
  intuition.
  
(*   try repeat rewrite and_assoc in H. *)
  destruct H as (((((((Hiso & Hancs & Hvs & Hcons &  HPrecond ) 
  & Hcurpart)
   & Hmult) & 
                 Hnotmult) & Hsh2root) & HnblL) & Hidxaddr).
                  destruct Hcurpart as ( Hancestors & Hcurpart & Hnewprops).
                  clear Hancestors. 
                 intuition.
  eapply Hcurpart.
  exists sh2.
  split; trivial.
  split. 
  unfold consistency in *.
  destruct Hcons as (Hprdesc & _ & _  & _ & Hpr  & _). 
  unfold partitionDescriptorEntry in Hprdesc.
  generalize (Hprdesc descParent Hcurpart); clear Hprdesc; intros Hprdesc.     
  assert (sh2idx = PDidx \/ sh2idx = sh1idx \/ sh2idx = sh2idx \/ sh2idx = sh3idx
   \/ sh2idx = PPRidx  \/ sh2idx = PRidx ) as Htmp 
  by auto.
  generalize (Hprdesc sh2idx Htmp); clear Hprdesc; intros Hprdesc.
  destruct Hprdesc as (Hidxsh2 & _& Hentry).
  destruct Hentry as (page1 & Hpd & Hnotnull).
  subst.
  unfold nextEntryIsPP in *; destruct (StateLib.Index.succ sh2idx);
   [destruct (lookup descParent i (memory s) beqPage beqIndex)
   as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hsh2root | 
   now contradict Hsh2root | 
   subst ; assumption| 
   now contradict Hsh2root| 
   now contradict Hsh2root ]  
   |now contradict Hsh2root] | now contradict Hsh2root].
  left; split; trivial.
  intros ptsh2. simpl.  
   (** simplify the new precondition **)     
  eapply WP.weaken.
  intros.
  Focus 2.
  intros.
  destruct H as (H0 & H1).
  assert( (getTableAddrRoot' ptsh2 sh2idx descParent va s /\ ptsh2 = defaultPage) \/
  (forall idx : index,
  StateLib.getIndexOfAddr va fstLevel = idx ->
   isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s)).
  { destruct H1 as [H1 |H1].
    + left. trivial. 
    + right. intros idx Hidx.
      destruct H1 as (Hget  & Hnew & H1).
      split. 
      generalize (H1 idx Hidx);clear H1;intros H1.
      destruct H1 as [(_& Hfalse) | [(Hpe &Htrue) | (_&Hfalse)]].
       - contradict Hfalse.
         unfold sh2idx, sh1idx.
         apply indexEqFalse ;
         assert (tableSize > tableSizeLowerBound).
         apply tableSizeBigEnough.
         unfold tableSizeLowerBound in *.
         omega.  apply tableSizeBigEnough.
         unfold tableSizeLowerBound in *.
         omega. apply tableSizeBigEnough. omega.
      - assumption.
      - contradict Hfalse.
        unfold PDidx. unfold sh2idx.
        apply indexEqFalse;
        assert (tableSize > tableSizeLowerBound).
        apply tableSizeBigEnough.
        unfold tableSizeLowerBound in *.
        omega.  apply tableSizeBigEnough.
        unfold tableSizeLowerBound in *.
        omega. apply tableSizeBigEnough. omega.
      - assumption.  }
  assert (HP := conj H0 H).
  pattern s in HP.
  eapply HP.
  (** comparePageToNull **) 
  eapply WP.bindRev.
  eapply Invariants.comparePageToNull.
  intro ptsh2Isnull. simpl.
  case_eq ptsh2Isnull.
  intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition.
  intros Hptsh2NotNull.
  (** readVirtual **)
  eapply bindRev.
  eapply weaken.
  eapply Invariants.readVirtual.
  simpl; intros.
  split.
  pattern s in H.
  eapply H.
  destruct H as 
  ((((((((Hprops & Hi ) & Hcurpart)& Hmult) & Hnotmult) & Hsh2root) & HnblL)
           & Hidxaddr)).
           
  destruct Hi as (  _ & Hnewprops).
 intuition.
  subst.
  apply beq_nat_false in H.
  now contradict H.
  assert( Hva : forall idx : index,
      StateLib.getIndexOfAddr va fstLevel = idx ->
      isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial. 
  apply Hva; trivial.
  intros vaInAncestor.
  simpl.
  (** getParent **)
  eapply bindRev.
  eapply weaken.
  eapply Invariants.getParent.
  intros.
  simpl.
  split.
  pattern s in H.
  eapply H. unfold propagatedProperties in *.  
  intuition.
  intros ancestor; simpl.
  (** getPd **)
  eapply bindRev.
  eapply weaken.
  eapply Invariants.getPd.
  simpl; intros.
  split.
  pattern s in H.
  eapply H. split.
  unfold propagatedProperties in H.
  unfold consistency in H.
  intuition.
  destruct H.
  unfold propagatedProperties in H.
  assert(Hkk : partitionsIsolation s /\
              kernelDataIsolation s /\
              verticalSharing s /\
              consistency s /\ In descParent (getPartitions MALInternal.multiplexer s) /\
           multiplexer = MALInternal.multiplexer /\ 
           false = StateLib.Page.eqb descParent multiplexer /\
         nextEntryIsPP descParent sh2idx sh2 s /\ Some L = StateLib.getNbLevel /\
       StateLib.getIndexOfAddr va fstLevel = lastIndex /\
      (getTableAddrRoot' ptsh2 sh2idx descParent va s /\ ptsh2 = defaultPage \/
       (forall idx : index,
        StateLib.getIndexOfAddr va fstLevel = idx -> 
        isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s)) /\ 
        (defaultPage =? ptsh2) = false /\ isVA' ptsh2 lastIndex vaInAncestor s) by intuition.
  destruct Hkk as (Hiso & Hancs & Hvs & Hcons  & Ha & Hb & Hc & Hd & He & Hf  
                  &  [(Hi & Hfalse) | Hi] & Hj & Hk ).  
  subst. apply beq_nat_false in Hj.
  now contradict Hj.
  unfold consistency in Hcons.
  destruct Hcons as (_ & _& _& _ & _ & _ & _ & Hparent ).
  unfold parentInPartitionList in *.
  apply Hparent with descParent; trivial.
  intros pdAncestor. (* 
  unfold setAccessible.
  simpl.
  eapply bindRev.
(** setAccessible **)
  unfold setAccessible.
  { *) eapply bindRev.
    (** getDefaultVAddr **)
    eapply weaken.
    eapply Invariants.getDefaultVAddr.
    simpl.
    intros.
    pattern s in H.
    eapply H.
    intros defaultV.
    simpl.
    eapply bindRev.
    (**   VAddr.eqbList **)
    eapply weaken.
    eapply Invariants.VAddr.eqbList.
    simpl.
    intros.
    pattern s in H.
    eapply H.
    intros isdefaultVA.
    (** case negb isdefaultVA **)
    case_eq (isdefaultVA).
    -  intros.
  eapply weaken.
  eapply WP.ret.
  intros.
  simpl. intuition. 
    - intros isdefaultVAT.
      eapply bindRev.
      (** getTableAddr **)
      eapply WP.weaken. 
      apply getTableAddr.
      simpl.
      intros s H.
      split.
      try repeat rewrite and_assoc in H.
      pattern s in H. 
      eapply H. 
      unfold propagatedProperties in H. 
      split.
      intuition.
      assert(Hcons : consistency s) by intuition.
      unfold consistency in *.
      destruct Hcons as (Hpd & _& _& _ & _ & _ & _ & Hparent & _ & _).
      unfold parentInPartitionList in *. 
      instantiate (2:= ancestor).
      split.
      apply Hparent with descParent; intuition.
       
      instantiate (1:= PDidx).
      split. intuition.
      exists pdAncestor.
      split. intuition.
      split. 
      unfold consistency in *.
(*       destruct Hcons as (Hpd & _& _& _ & _ & _ & _ & Hparent).  *)
      unfold partitionDescriptorEntry in Hpd.
      unfold parentInPartitionList in *.
      subst.
      assert(Hpartancestor : In ancestor (getPartitions MALInternal.multiplexer s)).
      {       apply Hparent with descParent; intuition. } 
      generalize (Hpd ancestor Hpartancestor); clear Hpd; intros Hpd.     
      assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/PDidx = sh3idx
              \/ PDidx = PPRidx  \/ PDidx = PRidx ) as Htmp 
            by auto.
      generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry).
      destruct Hentry as (page1 & Hpd & Hancesnotnull).
      subst.
      assert (Hrootances : nextEntryIsPP ancestor PDidx pdAncestor s) by intuition.
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx);
       [destruct (lookup ancestor i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootances |
        now contradict Hrootances | 
       subst ; assumption| now contradict Hrootances| now contradict Hrootances ]  
       |now contradict Hrootances] | now contradict Hrootances].
      subst. left. split;intuition.
      intro ptvaInAncestor. simpl.
       (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      Focus 2.
      intros.
      destruct H as (H0 & H1).
      assert( (getTableAddrRoot' ptvaInAncestor PDidx ancestor vaInAncestor s /\ ptvaInAncestor = defaultPage) \/
              (forall idx : index,
               StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
              isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s)).
      { destruct H1 as [H1 |H1].
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
           - assumption.
           - assumption.  }  
      do  15 (* 6 *) rewrite <- and_assoc in H0.
      destruct H0 as (H0 & Hor &  Htrue & Hrest).
      destruct Hor as [( _ & Hfalse) |Htableroot].
      rewrite Hfalse in Htrue.
      apply beq_nat_false in Htrue.
      now contradict Htrue.
      clear H1.
      do 2 rewrite <- and_assoc in Hrest.
      destruct Hrest as (Hrest & Hdef & Hvanotnull).
      rewrite Hdef in Hvanotnull. clear Hdef.
      try repeat rewrite and_assoc in H0.
      assert (HP :=conj(conj (conj(conj (conj H0 Htableroot) Htrue )Hrest) H) isdefaultVAT).
      pattern s in HP.
      eapply HP.
  (** comparePageToNull **) 
      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro ptvaInAncestorIsnull. simpl.
      case_eq ptvaInAncestorIsnull.
      Focus 2.
      intros HptvaInAncestorIsnulll.
  (** StateLib.getIndexOfAddr **)                
      eapply WP.bindRev.
      eapply WP.weaken.
      eapply Invariants.getIndexOfAddr.
      { simpl. intros.
        do 2 rewrite  and_assoc in H.
        destruct H as (H & [(Hptchild& Hnull) | Hptchild] & Hptchildnotnull).
        + subst. contradict Hptchildnotnull. intro Hnull.
          destruct Hnull.
          apply beq_nat_false in H1. intuition.
        +
          assert (HP := conj (conj H Hptchild) Hptchildnotnull).
          try repeat rewrite and_assoc in HP.
          pattern s in HP.
          eapply HP.  }
      intros idxva.
      simpl.
      eapply bindRev; simpl;[|intros []].
      (** writeAccessible **)
      eapply WP.weaken.
      eapply WP.writeAccessible.
      intros. simpl.
      assert (exists entry0 : Pentry,
        lookup ptvaInAncestor idxva (memory s) beqPage beqIndex = Some (PE entry0)) as Hlookup.
      { apply isPELookupEq.
        assert (forall idx : index,
        StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
        isPE ptvaInAncestor idx s /\
        getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s ) as H2 by intuition.
        destruct H. 
        apply H2 in H0. intuition. }
      destruct Hlookup as (entry & Hlookup).
      exists entry ; split;trivial. 
      try repeat rewrite and_assoc in H.
      do 9 rewrite <- and_assoc in H.
      destruct H as (Hsplit & Hfalse & Hrest).
      assert(Heqphy : phypage = pa entry).
      {    destruct Hsplit as 
(((((((((Hprops  & _ )  & Hmult)& Hnotnul1)  
 & Hgetroot ) & Hnotnull2 ) & Hidx )
           & Hpresent ) & Huser ) &Hep).
           destruct Hrest as (_ & Hnotmult & Hppsh2 & HL & Hlstidx & Hva & 
           Hnotnul3 & Hva' & Hppparent & Hpppd & Hgetroot2 & Hdef & Hidxancestor).
         intuition. subst.
        unfold isAccessibleMappedPageInParent in *.
        assert (HgetVirt : getVirtualAddressSh2 sh2 s va  = Some vaInAncestor).
        apply isVaInParent with descParent ptsh2;trivial.
        apply nextEntryIsPPgetSndShadow in Hppsh2.
        rewrite Hppsh2 in *.
        rewrite HgetVirt in *.
        rewrite nextEntryIsPPgetParent in * .
        rewrite Hppparent in *. 
        apply nextEntryIsPPgetPd in Hpppd .
        rewrite Hpppd in *.
        case_eq(getAccessibleMappedPage pdAncestor s vaInAncestor);
        intros * Hacce;
        rewrite Hacce in *;try now contradict Hfalse.
        unfold getAccessibleMappedPage in Hacce.
        assert( isPE ptvaInAncestor  (StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\ 
        getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) as (Hve & Hroot ).
        apply Hgetroot2;trivial.
        unfold getTableAddrRoot in *.
        destruct Hroot as (_ & Hroot).
        rewrite <- nextEntryIsPPgetPd in *.
        apply Hroot in  Hpppd.
        clear Hroot.
        destruct Hpppd as (nbL & HnbL & stop & Hstop & Hind).
        subst.
        rewrite <- HnbL in *.
        assert(Hgetind : getIndirection pdAncestor vaInAncestor nbL (nbLevel - 1) s  
        = Some ptvaInAncestor).
        apply getIndirectionStopLevelGT2 with (nbL+1);trivial.
        omega.
        apply getNbLevelEq in HnbL.
        rewrite HnbL.
        unfold CLevel.
        case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
        simpl;trivial.
        assert(0<nbLevel) by apply nbLevelNotZero.
        omega.
        rewrite Hgetind in *.
        rewrite H in *.
        destruct ( StateLib.readPresent ptvaInAncestor
        (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
        (memory s));try now contradict Hacce.
        destruct b;try now contradict Hacce.
        destruct ( StateLib.readAccessible ptvaInAncestor
        (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
        (memory s)); try now contradict Hacce.
        destruct b; try now contradict Hacce.
        unfold StateLib.readPhyEntry in *. 
        rewrite Hlookup in *.
        apply beq_nat_true in Hfalse.
        inversion Hacce.
        subst.
        destruct phypage; destruct (pa entry).
        simpl in *.
        subst.
        f_equal; apply proof_irrelevance. }
      assert (Htrue : isAccessibleMappedPageInParent ancestor vaInAncestor phypage s = true).
      { assert(Hcons : consistency s).
        { unfold propagatedProperties in *.
          intuition. }
        unfold consistency in Hcons.
        rewrite Heqphy.
        destruct Hsplit as 
(((((((((Hprops  & _ )  & Hmult)& Hnotnul1)  
 & Hgetroot ) & Hnotnull2 ) & Hidx )
           & Hpresent ) & Huser ) &Hep).
           destruct Hrest as (_ & Hnotmult & Hppsh2 & HL & Hlstidx & Hva & 
           Hnotnul3 & Hva' & Hppparent & Hpppd & Hgetroot2 & Hdef & Hidxancestor).
 
        apply mimi with descParent va phypage ptvaInAncestor ptsh2 pdAncestor;
        subst;intuition.
        subst;assumption. }
      repeat rewrite and_assoc in Hsplit.
      destruct Hsplit as (Hprops & Hsplit).
(*       unfold propagatedProperties in *.
      do 73 rewrite <- and_assoc in Hprops.
      destruct Hprops as (Hprops & xx & Hprops2). 
            repeat rewrite and_assoc in Hprops. *)
      assert (Hnewprops := conj  Hprops  Hsplit).
      assert (H := conj (conj Hnewprops Htrue) Hrest).
      simpl.
      clear Hnewprops.
    (*   repeat rewrite and_assoc in H. *)
      pattern s in H.
      match type of H with 
      | ?HT s => instantiate (1 := fun tt s => HT s  /\ 
                  entryUserFlag ptvaInAncestor idxva false s /\
                  isEntryPage ptvaInAncestor idxva phypage s /\
                  entryPresentFlag ptvaInAncestor idxva true s  ) 
      end.
      simpl.
      set (s' := {|
      currentPartition := currentPartition s;
      memory := add ptvaInAncestor idxva
                (PE
                   {|
                   read := read entry;
                   write := write entry;
                   exec := exec entry;
                   present := present entry;
                   user := false;
                   pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
                   simpl in *.                    
      assert(Hmult : multiplexer = MALInternal.multiplexer) by intuition. 
      subst.
      simpl.
      unfold propagatedProperties in *. 
      do 7 rewrite and_assoc.
      clear Hrest  Hsplit  Hprops.
      split.
      
    (** partitionsIsolation **) 
      assert (partitionsIsolation s) as Hiso. intuition.
      unfold partitionsIsolation in *.
      assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
      apply getPartitionsUpdateUserFlag; trivial.
      subst. 
      rewrite Hpartions. clear Hpartions.
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
      assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
      apply getPartitionsUpdateUserFlag; trivial. 
      rewrite Hpartions in *.
      clear Hpartions.
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
      assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite Hpartions. clear Hpartions.
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
      unfold consistency in *.
      split.
      (** partitionDescriptorEntry **)
      apply partitionDescriptorEntryUpdateUserFlag;trivial.
      intuition.
      (** dataStructurePdSh1Sh2asRoot **)
      destruct Hcons as (Hpe & Hpd & Hsh1 & Hsh2 & Hcurpartlist & 
      Hnodupmapped & Hnodupconfig & Hparent & Hsh1struct).
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      (** currentPartitionInPartitionsList **)
      split.
      unfold currentPartitionInPartitionsList in *.
      simpl in *. subst. 
      assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite Hpartions. assumption.
      (** noDupMappedPagesList **)  
      split.    
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
      split.
      (** noDupConfigPagesList **)
      apply getIndirectionsNoDupUpdateUserFlag; trivial.
      split.
      (** parentInPartitionList **)
      unfold parentInPartitionList in *.
      assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart.
      intros partition HgetParts parent Hroot.
      generalize (Hparent partition HgetParts); clear Hparent; intros Hparent; trivial.
      apply  nextEntryIsPPUpdateUserFlag' in  Hroot.
      apply Hparent; trivial.
      split.
      (** accessibleVAIsNotPartitionDescriptor **)
     unfold s'.
      subst.
      clear IHn.
      destruct Hsh1struct as (Hsh1struct & HaccessRec & Hcons1 & Hcons2).
      destruct H as ((( H & Hi ) & H1 ) & H2). 
      destruct Hi as (_ & Hi).
      intuition.
      subst.
      apply accessibleVAIsNotPartitionDescriptorUpdateUserFlag  with level ancestor   
        pdAncestor;trivial.
      assert(Hparentpart : parentInPartitionList s) by trivial.
      unfold parentInPartitionList in *.
      apply Hparent with descParent;trivial. 
       assert(Hget : forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
      isPE ptvaInAncestor idx s /\ 
      getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
      assert(  isPE ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\ 
      getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s ) as (_ & Hroot).
      apply Hget;split;trivial.
      assumption.
      apply nextEntryIsPPgetPd;trivial.
      subst.
      assert(HaccessInParent : isAccessibleMappedPageInParent descParent va (pa entry) s = true)
       by trivial.
       unfold isAccessibleMappedPageInParent in HaccessInParent.
       (** Here we use the property already present into the precondition : 
            *)
       assert(Hcursh2 : nextEntryIsPP descParent sh2idx sh2 s ) by trivial.
      apply nextEntryIsPPgetSndShadow in Hcursh2.
      rewrite Hcursh2 in HaccessInParent.
      assert(Hvainparent : getVirtualAddressSh2 sh2 s va = Some vaInAncestor).
      { assert(Hxx : forall idx : index,
        StateLib.getIndexOfAddr va fstLevel = idx ->
        isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
        assert(Hgetva : isVA ptsh2 (StateLib.getIndexOfAddr va fstLevel) s /\ 
        getTableAddrRoot ptsh2 sh2idx descParent va s).
        apply Hxx;trivial. clear Hxx.
        destruct Hgetva as (Hva & Hgetva).
        assert(Hisva : isVA' ptsh2 (StateLib.getIndexOfAddr va fstLevel) vaInAncestor s) 
        by trivial.
        unfold getVirtualAddressSh2.
        unfold getTableAddrRoot in Hgetva.
        destruct Hgetva as (_ & Hgetva).
        assert(HcurSh2 : nextEntryIsPP descParent sh2idx sh2 s).
        rewrite  nextEntryIsPPgetSndShadow ;trivial.
        apply Hgetva in HcurSh2.
        destruct HcurSh2 as (nbL & HnbL & stop & Hstop & Hind).
        rewrite <- HnbL.
        subst.
        assert(Hgetind : getIndirection sh2 va nbL (nbLevel - 1) s = Some ptsh2).
        apply getIndirectionStopLevelGT2 with (nbL + 1);trivial.
        omega.
        apply getNbLevelEq in HnbL.
        rewrite HnbL.
        unfold CLevel.
        case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
        simpl;trivial.
        assert(0<nbLevel) by apply nbLevelNotZero.
        omega.
        rewrite Hgetind.
        assert (Hptnotnull : (defaultPage =? ptsh2) = false) by trivial.
        rewrite Hptnotnull.
        unfold  isVA' in *. 
        unfold StateLib.readVirtual.
        destruct(lookup ptsh2 (StateLib.getIndexOfAddr va fstLevel) (memory s) beqPage beqIndex ); 
        try now contradict Hisva.
        destruct v;try now contradict Hisva.
        subst. trivial. }
      rewrite Hvainparent in *.
      assert(Hgetparent : StateLib.getParent descParent (memory s) = Some ancestor).
      { apply nextEntryIsPPgetParent;trivial. }
      rewrite Hgetparent in *.
      assert(Hgetpdparent : StateLib.getPd ancestor (memory s) = Some pdAncestor).
      { apply nextEntryIsPPgetPd;trivial. }
      rewrite Hgetpdparent in *.
      case_eq(getAccessibleMappedPage pdAncestor s vaInAncestor ); intros * Hi .
      rewrite Hi in *.
      unfold getAccessibleMappedPage in Hi.
      case_eq (StateLib.getNbLevel);intros * Hi2 ; rewrite Hi2 in *;
       try now contradict Hi.
      assert(Hancestor : forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
      isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by 
      trivial.
      assert(Hget : isPE ptvaInAncestor ( StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\
            getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s).
      apply Hancestor; clear Hancestor;
      trivial.
      destruct Hget as (Hva & Hget).
      unfold getTableAddrRoot in Hget.
      destruct Hget as (_ & Hget).
      apply nextEntryIsPPgetPd in Hgetpdparent.
      apply Hget in Hgetpdparent.
      destruct Hgetpdparent as (nbL & HnbL & stop & Hstop & Hgettable).
      clear Hget.
      rewrite <- HnbL in *.
      inversion Hi2.
      subst.
      assert(Hind :getIndirection pdAncestor vaInAncestor l (nbLevel - 1) s = Some ptvaInAncestor).
      apply getIndirectionStopLevelGT2 with (l+1);trivial.
      omega.
      apply getNbLevelEq in HnbL.
      rewrite HnbL.
      unfold CLevel.
      case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
      simpl;trivial.
      assert(0<nbLevel) by apply nbLevelNotZero.
      omega.
      rewrite Hind in *.
      assert (Hnotnull : (defaultPage =? ptvaInAncestor) = false) by trivial.
      rewrite Hnotnull in *.
      destruct (StateLib.readPresent ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
      (memory s)); try now contradict Hi.
      destruct b; try now contradict Hi.
      destruct(StateLib.readAccessible ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
      (memory s)); try now contradict Hi.
      destruct b.
      unfold StateLib.readPhyEntry in *.
      rewrite Hlookup in *.
      symmetry; assumption.
      now contradict Hi.
      rewrite Hi in *. 
      now contradict HaccessInParent.
   (* accessibleChildPhysicalPageIsAccessibleIntoParent *)
      destruct Hsh1struct as (Hsh1struct & HaccessRec & Hcons1 & Hcons2).
      destruct H as ((( H & Hi ) & H1 ) & H2). 
      destruct Hi as (Hancestor & Hi).
      unfold s'.
      intuition. 
      subst.
      clear IHn.
      apply accessibleChildPhysicalPageIsAccessibleIntoParentUpdateUserFlagFlase
      with level ancestor pdAncestor va ptsh2 descParent pt;trivial.
      assert(Hparentpart : parentInPartitionList s).
      unfold consistency in *; intuition.
      unfold parentInPartitionList in *.
      apply Hparentpart with descParent;trivial.
      (* noCycleInPartitionTree *)
      assert(Hdiff : noCycleInPartitionTree s) by trivial.
      unfold noCycleInPartitionTree in *.
      intros parent partition Hparts Hparentpart.
      simpl in *.
      assert (getPartitions multiplexer {|
              currentPartition := currentPartition s;
              memory := add ptvaInAncestor idxva
                          (PE
                             {|
                             read := read entry;
                             write := write entry;
                             exec := exec entry;
                             present := present entry;
                             user := false;
                             pa := pa entry |}) (memory s) beqPage beqIndex |}
               = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart in *. clear HgetPart.
      assert(HgetParent : getAncestors partition
                {|
                   currentPartition := currentPartition s;
                   memory := add ptvaInAncestor idxva
                               (PE
                                  {|
                                  read := read entry;
                                  write := write entry;
                                  exec := exec entry;
                                  present := present entry;
                                  user := false;
                                  pa := pa entry |}) (memory s) beqPage beqIndex |} = 
                      getAncestors partition  s).
      apply getAncestorsUpdateUserFlag;trivial.
      rewrite HgetParent in *; clear HgetParent.
      apply Hdiff;trivial.
      (* configTablesAreDifferent *)
      assert(Hconfigdiff : configTablesAreDifferent s) by trivial.
      unfold configTablesAreDifferent in *.
      simpl in *.
      fold s'.
      intros partition1 partition2 Hpart1 Hpart2 Hdiff.
      assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart in *. clear HgetPart.
      assert(Hconfig : getConfigPages partition1 s' = getConfigPages partition1 s).
      apply getConfigPagesUpdateUserFlag;trivial.
      rewrite Hconfig;clear Hconfig.
      assert(Hconfig : getConfigPages partition2 s' = getConfigPages partition2 s).
      apply getConfigPagesUpdateUserFlag;trivial.
      rewrite Hconfig;clear Hconfig.
      apply Hconfigdiff;trivial.
      rename H into Hcond.
      (** isChild **)
      assert(Hchid : isChild s) by intuition.
      unfold isChild in *.
      simpl in *.
      intros partition parent Hparts Hgetparent.
      rewrite getPartitionsUpdateUserFlag in *;trivial.
      rewrite getParentUpdateUserFlag in *;trivial.
      rewrite getChildrenUpdateFlagUser;trivial.
      apply Hchid;trivial.
          (** isPresentNotDefaultIff **)
    assert (Hpres : isPresentNotDefaultIff s) by intuition.
    unfold isPresentNotDefaultIff in *.
    unfold s'.
    simpl.
    intros table idx.
    rewrite readPhyEntryUpdateUserFlag;trivial.
    rewrite readPresentUpdateUserFlag;trivial.
    (** physicalPageNotDerived **)
    admit. (* physicalPageNotDerived *)
  (** Propagated properties **)
      assert(Hi2 : StateLib.getIndexOfAddr va fstLevel = lastIndex) by intuition.
      {  intuition trivial. 
        + apply nextEntryIsPPUpdateUserFlag ; assumption.
        + assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr descChild fstLevel = idx ->
                      isPE ptRefChild idx s /\ 
                      getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
          assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
          intuition.
          generalize (Hi idx HP); clear H23; intros (H23 & _). 
          apply isPEUpdateUserFlag; assumption.
        + assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr descChild fstLevel = idx ->
                      isPE ptRefChild idx s /\ 
                      getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
          assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
          intuition.
          generalize (Hi idx HP); clear H23; intros (_ & H23).         
          unfold getTableAddrRoot in H23.
          unfold getTableAddrRoot.
          destruct H23 as (Hor & Htableroot).
          split;trivial.
          intros.         
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
          assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          left.
          clear IHn.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst.

            rewrite Hisancestor in *.
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptRefChild (getConfigPages descParent s)).
            apply isConfigTable with descChild;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
            {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            apply isAncestorTrans2 with descParent;trivial.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptRefChild (getConfigPages (currentPartition s) s)).
            apply isConfigTable with descChild;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.

            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
(** partitions are diffrent then config pages are different *)
        + assert(Hi3 : forall idx : index,
                        StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                        isPE ptPDChild idx s /\ 
                        getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
          assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
          intuition.
          generalize (Hi3 idx HP);clear H7;intros (H7 & _).
          apply isPEUpdateUserFlag;  assumption.
        + assert(Hi3 : forall idx : index,
                        StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                        isPE ptPDChild idx s /\ 
                        getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
          assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
          intuition.
          generalize (Hi3 idx HP); clear H7; intros (_ & H7). 
          unfold getTableAddrRoot in H7.
           unfold getTableAddrRoot.
          destruct H7 as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi4 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi4.
        
          generalize(Htableroot tableroot Hi4 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagSameValue;trivial.
        + assert(Hi: forall idx : index,
                      StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                      isPE ptSh1Child idx s /\ 
                      getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
          assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
          generalize (Hi idx Hi1);clear H7;intros (H7 & _).
          apply isPEUpdateUserFlag;assumption.
        + assert(Hi: forall idx : index,
                      StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                      isPE ptSh1Child idx s /\ 
                      getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
          assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
          generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
          unfold getTableAddrRoot in H7'.
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert (Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.     
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split;trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
                  assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst.
            clear IHn.
            rewrite Hisancestor in *.
            left.
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptSh1Child (getConfigPages descParent s)).
            apply isConfigTable with shadow1;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            clear IHn.
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
                        {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            apply isAncestorTrans2 with descParent;trivial.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptSh1Child (getConfigPages (currentPartition s) s)).
            apply isConfigTable with shadow1;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            left.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2. 
        + assert(Hi1 : forall idx : index,
                        StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                        isPE ptSh2Child idx s /\ 
                        getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
          assert(Hi4 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
          generalize (Hi1 idx Hi4);clear H7;intros (H7 & _).
          apply isPEUpdateUserFlag;assumption.
        + assert(Hi1 : forall idx : index,
                        StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                        isPE ptSh2Child idx s /\ 
                        getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
          assert(Hi4 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
          generalize (Hi1 idx Hi4);clear H7;intros (H7 & H7').
          unfold getTableAddrRoot in H7'.
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.       
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split;trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.

        assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
        unfold isAncestor in *.
        destruct Hisancestor as [Hisancestor | Hisancestor].
        - subst.
          clear IHn.
          rewrite Hisancestor in *.
          left.
          unfold consistency in *.
          assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
          assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
          unfold configTablesAreDifferent in *.
          assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
          apply Hconfigdiff;trivial.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          assert(Hin1 : In ptSh2Child (getConfigPages descParent s)).
          apply isConfigTable with shadow2;trivial.
          intuition.
          assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
          apply isConfigTable with vaInAncestor;trivial.
          intuition.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          unfold disjoint in *.
          apply Hdisjoint in Hin1.
          unfold not;intros; subst.
          now contradict Hin2.
        - unfold consistency in *.
          subst.
          clear IHn.
          assert(In (currentPartition s) (getPartitions multiplexer s)).
          unfold currentPartitionInPartitionsList in *.
          intuition.
          assert((currentPartition s) <> ancestor).
          { unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            apply isAncestorTrans2 with descParent;trivial.
            apply nextEntryIsPPgetParent;trivial. }
          assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
          unfold configTablesAreDifferent in *. 
          assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
          apply Hconfigdiff;trivial.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          assert(Hin1 : In ptSh2Child (getConfigPages (currentPartition s) s)).
          apply isConfigTable with shadow2;trivial.
          intuition.
          assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
          apply isConfigTable with vaInAncestor;trivial.
          intuition.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          unfold disjoint in *.
          left.
          apply Hdisjoint in Hin1.
          unfold not;intros; subst.
          now contradict Hin2. 
        + assert(Hi : forall idx : index,
                        StateLib.getIndexOfAddr list fstLevel = idx ->
                        isPE ptConfigPagesList idx s /\ 
                        getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
          assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
          generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
          apply isPEUpdateUserFlag;assumption.
        + assert(Hi : forall idx : index,
                        StateLib.getIndexOfAddr list fstLevel = idx ->
                        isPE ptConfigPagesList idx s /\ 
                        getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
          assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
          generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
          unfold getTableAddrRoot in H7'.
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.     
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & Hind).
          exists nbL. split;trivial.
          destruct Hind as (stop  & Hstop & Hind). 
          rewrite <- Hind.
          exists stop; split; trivial.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
          assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst.
            clear IHn.
            rewrite Hisancestor in *.
            left.
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptConfigPagesList (getConfigPages descParent s)).
            apply isConfigTable with list;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            clear IHn.
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
                        {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            apply isAncestorTrans2 with descParent;trivial.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptConfigPagesList (getConfigPages (currentPartition s) s)).
            apply isConfigTable with list;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            left.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2. 
        + apply nextEntryIsPPUpdateUserFlag;assumption.  
        + assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr descChild fstLevel = idx ->
                      isVE ptRefChildFromSh1 idx s /\
                      getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
          assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
          generalize (Hi idx Hi1); clear H7; intros (H7 & H7').      
          apply isVEUpdateUserFlag; assumption.
        + assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr descChild fstLevel = idx ->
                      isVE ptRefChildFromSh1 idx s /\
                      getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
          assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
          generalize (Hi idx Hi1); clear H7; intros (H7 & H7').
          unfold getTableAddrRoot in H7'.
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi4 : nextEntryIsPP currentPart sh1idx tableroot s') by intuition.
          apply nextEntryIsPPUpdateUserFlag' in Hi4.    
          generalize(Htableroot tableroot Hi4 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & Hind).
          exists nbL. split;trivial.
          destruct Hind as (stop  & Hstop & Hind). 
          rewrite <- Hind.
          exists stop; split; trivial. 
          apply getIndirectionUpdateUserFlag;trivial.
        + assert(Hi : exists va : vaddr,
                        isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
                        beqVAddr defaultVAddr va = derivedRefChild)
                        by intuition.
          destruct Hi as  (va0 & Hv& Hnotnull).
          exists va0. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
        + assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isVE ptPDChildSh1 idx s /\ 
                      getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
          assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
          generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
          apply isVEUpdateUserFlag;assumption.
        + assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isVE ptPDChildSh1 idx s /\ 
                      getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
          assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
          generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
          unfold getTableAddrRoot in H7'.
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.    
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & Hind).
          exists nbL. split;trivial.
          destruct Hind as (stop  & Hstop & Hind). 
          rewrite <- Hind.
          exists stop; split; trivial.
          apply getIndirectionUpdateUserFlag;trivial.
        + assert(Hi : exists va : vaddr,
                      isEntryVA ptPDChildSh1 idxPDChild va s /\ 
                      beqVAddr defaultVAddr va = derivedPDChild) by trivial. 
          destruct Hi as  (va0 & Hv& Hnotnull).
          exists va0. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
        + assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                      isVE ptSh1ChildFromSh1 idx s /\ 
                      getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
          assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
          generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
          apply isVEUpdateUserFlag;assumption.
        + assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                      isVE ptSh1ChildFromSh1 idx s /\ 
                      getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
          assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
          generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
          unfold getTableAddrRoot in H7'.
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.      
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & Hind).
          exists nbL. split;trivial.
          destruct Hind as (stop  & Hstop & Hind). 
          rewrite <- Hind.
          exists stop; split; trivial.
          apply getIndirectionUpdateUserFlag;trivial.
        + assert(Hi : exists va : vaddr,
          isEntryVA ptSh1ChildFromSh1 idxSh1 va s /\ beqVAddr defaultVAddr va = derivedSh1Child) 
          by trivial.
          destruct Hi as  (va0 & Hv& Hnotnull).
          exists va0. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
        + assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                      by trivial. 
          assert(Hi4 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
          generalize (Hi idx Hi4);clear H7;intros (H7 & H7').
          apply isVEUpdateUserFlag;assumption.
        + assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                      by trivial. 
          assert(Hi4 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
          generalize (Hi idx Hi4);clear H7;intros (H7 & H7').
          unfold getTableAddrRoot in H7'.
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
         
          generalize(Htableroot tableroot Hi3);clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & Hind).
          exists nbL. split;trivial.
          destruct Hind as (stop  & Hstop & Hind). 
          rewrite <- Hind.
          exists stop; split; trivial.
          apply getIndirectionUpdateUserFlag;trivial.
        + assert(Hi : exists va : vaddr, isEntryVA childSh2 idxSh2 va s /\ 
                      beqVAddr defaultVAddr va = derivedSh2Child) by trivial.
          destruct Hi as  (va0 & Hv& Hnotnull).
          exists va0. split; [ apply isEntryVAUpdateUserFlag | ];trivial. 
        + assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isVE childListSh1 idx s /\ 
                      getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
          assert(Hi4 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
          generalize (Hi idx Hi4);clear H7;intros (H7 & H7').
          apply isVEUpdateUserFlag;assumption.
        + assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isVE childListSh1 idx s /\ 
                      getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
          assert(Hi4 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
          generalize (Hi idx Hi4);clear H7;intros (H7 & H7'). 
          unfold getTableAddrRoot in H7'.
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.

          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & Hind).
          exists nbL. split;trivial.
          destruct Hind as (stop  & Hstop & Hind). 
          rewrite <- Hind.
          exists stop; split; trivial.
          apply getIndirectionUpdateUserFlag;trivial.
        + trivial. assert(Hi : exists va : vaddr,
          isEntryVA childListSh1 idxConfigPagesList va s /\
          beqVAddr defaultVAddr va = derivedRefChildListSh1) by trivial.
                      intuition.
          destruct Hi as  (va0 & Hv& Hnotnull).
          exists va0. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      + apply isEntryPageUpdateUserFlag; trivial.
      + assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      + assert (Hfalse' : In phyPDChild (getConfigPagesAux partition s')); trivial.
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
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      + apply isEntryPageUpdateUserFlag; trivial.
      + assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      + assert (Hfalse' : In phySh1Child (getConfigPagesAux partition s')); trivial.
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
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      + apply isEntryPageUpdateUserFlag; trivial.
      + assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      + assert (Hfalse' : In phySh2Child (getConfigPagesAux partition s')); trivial.
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
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      + apply isEntryPageUpdateUserFlag; trivial.
      + assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      + assert (Hfalse' : In phyConfigPagesList (getConfigPagesAux partition s')); trivial.
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
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      + apply isEntryPageUpdateUserFlag; trivial. 
      + assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. 
        assert((getConfigPages partition s') = 
             (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        rewrite Hconfig in *.
        assert(Hii : forall partition : page,
            In partition (getPartitions multiplexer s) -> 
            In phyDescChild (getConfigPages partition s) -> False) by trivial.
        assert(Hfalse' : In phyDescChild (getConfigPages partition s)) by trivial.
        apply Hii in Hfalse';trivial. 
      + unfold isPartitionFalse. 
         unfold s'.
         cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial. 
         
(** Internal properties to propagate **)      
      + unfold s'.
        apply isAncestorUpdateUserFlag;trivial. 
      + destruct H.  
        unfold propagatedProperties in *.
        { assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
          apply getPartitionsUpdateUserFlag; trivial.
          rewrite Hpartions; assumption. }
       
      + apply isPEUpdateUserFlag;trivial. 
          assert(Hpe : forall idx : index,
                StateLib.getIndexOfAddr va fstLevel = idx -> isPE pt idx s /\ 
                getTableAddrRoot pt PDidx descParent va s) 
          by trivial.
           apply Hpe;trivial.
      +  assert(Hroot : isPE pt (StateLib.getIndexOfAddr va fstLevel ) s /\
          getTableAddrRoot pt PDidx descParent va s).
          assert(Hpe : forall idx : index,
           StateLib.getIndexOfAddr va fstLevel = idx -> isPE pt idx s /\ getTableAddrRoot pt PDidx descParent va s) 
            by trivial.
          apply Hpe;trivial.
          destruct Hroot as (Hve & Hroot). 
          unfold getTableAddrRoot in *.
          destruct Hroot as (Hor & Hroot).
          split;trivial.
          intros root Hpp.
          unfold s' in Hpp.
          apply nextEntryIsPPUpdateUserFlag' in Hpp.
          apply Hroot in Hpp.
          destruct Hpp as (nbL & HnbL & stop & Hstop & Hind).
          exists nbL ; split;trivial.
          exists stop;split;trivial.
          rewrite <- Hind.
          unfold s'.
          apply getIndirectionUpdateUserFlag;trivial. 
       +  apply entryPresentFlagUpdateUserFlag;trivial. 
       + apply entryUserFlagUpdateUserFlagSameValue;trivial.
       +  apply isEntryPageUpdateUserFlag;trivial. 
       +  subst. clear IHn.       
          assert(HisAccess : isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) s' =
          isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) s).
          { unfold isAccessibleMappedPageInParent.
            unfold s'.
            simpl.
            rewrite getSndShadowUpdateUserFlag;trivial.
            case_eq( StateLib.getSndShadow ancestor (memory s));
            intros * Hsh2 ;trivial.
            assert( Hvirt : getVirtualAddressSh2 p
                             {| currentPartition := currentPartition s;
                              memory := add ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                              (PE
                                 {|
                                 read := read entry;
                                 write := write entry;
                                 exec := exec entry;
                                 present := present entry;
                                 user := false;
                                 pa := pa entry |}) (memory s) beqPage beqIndex |} vaInAncestor =
                            getVirtualAddressSh2 p s vaInAncestor).
            { unfold getVirtualAddressSh2.
              assert(HnbL: Some L = StateLib.getNbLevel) by trivial.
              rewrite <- HnbL;trivial.
              rewrite getIndirectionUpdateUserFlag;trivial.
              destruct(getIndirection p vaInAncestor L (nbLevel - 1) s );trivial.
              simpl.
              rewrite readVirtualUpdateUserFlag;trivial. }
              rewrite Hvirt;trivial.
              case_eq (getVirtualAddressSh2 p s vaInAncestor );
              intros * Hvainances;trivial.
              rewrite getParentUpdateUserFlag;trivial.
              case_eq( StateLib.getParent ancestor (memory s)); 
              intros * HparentAcestor;trivial.
              rewrite getPdUpdateUserFlag.
              case_eq(StateLib.getPd p0 (memory s) );
              intros * Hpdparentances;trivial.
              assert( Haccessible : 
                        getAccessibleMappedPage p1
                          {|
                          currentPartition := currentPartition s;
                          memory := add ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                                      (PE
                                         {|
                                         read := read entry;
                                         write := write entry;
                                         exec := exec entry;
                                         present := present entry;
                                         user := false;
                                         pa := pa entry |}) (memory s) beqPage beqIndex |} v = 
                        getAccessibleMappedPage p1 s v).
              { symmetry.
                
                unfold consistency in *.
                assert (Hparentpart : parentInPartitionList s ) by  intuition.
                unfold parentInPartitionList in *.
                assert(Hancestor : In ancestor (getPartitions multiplexer s)).
                apply Hparentpart with descParent;trivial.
                apply getAccessibleMappedPageUpdateUserFlagDiffrentPartitions with ancestor p0;trivial.
                unfold consistency in *.
                intuition.
                assert(Hget : forall idx : index,
                        StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
                        isPE ptvaInAncestor idx s /\ 
                        getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
                destruct Hget with (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                as (Hpe & Hroot);
                trivial.
                apply Hparentpart with ancestor;trivial.
                apply nextEntryIsPPgetParent;trivial.
                assert(Hdiff : noCycleInPartitionTree s)
                by intuition.
                unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                apply parentIsAncestor.
                apply nextEntryIsPPgetParent;trivial.
              assert(Hdiff1 : p0 <> ancestor).
                              assert(Hdiff : noCycleInPartitionTree s)
                by intuition.
                unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                              apply parentIsAncestor.
                apply nextEntryIsPPgetParent;trivial.
              assert(Hdisjoint : configTablesAreDifferent s) by intuition.
              unfold configTablesAreDifferent in *.
              apply Hdisjoint;trivial.
              assert(Hparentinpart : parentInPartitionList s) by intuition.
              unfold parentInPartitionList in *.
              apply Hparentinpart with ancestor;trivial.
              rewrite nextEntryIsPPgetParent;trivial.
              unfold not;intros Hfalsei;subst.
              now contradict Hdiff1.
              }
              assert(Haccess : accessibleChildPhysicalPageIsAccessibleIntoParent s).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold accessibleChildPhysicalPageIsAccessibleIntoParent in *.
              assert(Hpde : partitionDescriptorEntry s ).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold partitionDescriptorEntry in *.
              assert(exists entry : page, nextEntryIsPP descParent PDidx entry s /\
                      entry <> defaultPage) as (pdParent & Hpp & Hnotnull).
              apply Hpde;trivial.
              left;trivial.
              clear Hpde.
              apply nextEntryIsPPgetPd in Hpp.
              rewrite Haccessible;trivial.
              assumption. }
          rewrite HisAccess.
          assumption.
        + apply nextEntryIsPPUpdateUserFlag; assumption. 
        + apply isVAUpdateUserFlag; intuition.
          assert( Hisva :  forall idx : index,
                      StateLib.getIndexOfAddr va fstLevel = idx ->
                      isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
                      apply Hisva; trivial. 
        + assert ( Hi : forall idx : index,
                  StateLib.getIndexOfAddr va fstLevel = idx ->
                  isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
          generalize (Hi lastIndex Hi2); clear H7; intros (_ & H7). 
          unfold getTableAddrRoot in *.
          destruct H7 as (Hii & Htableroot).
          split; trivial.
          intros.
          apply nextEntryIsPPUpdateUserFlag' in H7.      
          generalize(Htableroot tableroot H7 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          unfold getTableAddrRoot.
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply isVA'UpdateUserFlag; trivial. 
        + apply  nextEntryIsPPUpdateUserFlag; trivial. 
        + apply  nextEntryIsPPUpdateUserFlag; trivial. 
        + assert(Hi :forall idx : index,
              StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
              isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) 
              by trivial.
          assert(Hi3 : StateLib.getIndexOfAddr vaInAncestor fstLevel = idx) by trivial.
          generalize (Hi idx Hi3);clear H7;intros (H7 & _).
          apply isPEUpdateUserFlag;assumption. 
        + assert(Hi : forall idx : index,
          StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
          isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
          assert(Hi3 : StateLib.getIndexOfAddr vaInAncestor fstLevel = idx) by trivial.
          generalize (Hi idx Hi3); clear H7; intros (_ & H7). 
          unfold getTableAddrRoot in *.
          destruct H7 as (Hii & Htableroot).
          split;trivial.
          intros.
          apply nextEntryIsPPUpdateUserFlag' in H7.         
          generalize(Htableroot tableroot H7 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
      (** WriteAccessible property **) 
      + unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity. 
      + unfold isEntryPage.
        unfold s'.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        cbn.
        rewrite Hpairs.  cbn. reflexivity.
      + unfold entryPresentFlag.
        unfold s'.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        cbn.
        rewrite Hpairs.  
        cbn.
        unfold consistency in *.
        assert(Hpres : isPresentNotDefaultIff s ) by intuition.
        symmetry.
        apply phyPageIsPresent with ptvaInAncestor idxva s;trivial. }

(** setAccessible success **)
  simpl. subst. 
  (** recursion **)
  eapply weaken.
  eapply IHn.
  simpl. intros.
  assert(Hancestorpart : In ancestor (getPartitions MALInternal.multiplexer s)).
  { unfold propagatedProperties in *.
    unfold consistency in * .
    assert (Hparent : parentInPartitionList s) by intuition.
    unfold parentInPartitionList in *.
    apply Hparent with descParent; intuition. }
  assert (Hparentchild : In descParent (getChildren ancestor s)).
  unfold propagatedProperties in *.
  unfold consistency in *.
  assert(Hchildren : isChild s) by intuition.
  unfold isChild in *.
      apply Hchildren;trivial.
      intuition.
      apply nextEntryIsPPgetParent;intuition.
  assert(Hvs : verticalSharing s).
   { unfold propagatedProperties in *.
      unfold consistency in *.
      intuition. }
    unfold verticalSharing in *.
  assert(Hvsall : incl (getUsedPages descParent s) (getMappedPages ancestor s)).
  apply Hvs;trivial.
  clear Hvs.
  apply verticalSharing2 in Hvsall.
  unfold incl in *.
  generalize(Hvsall phypage);clear Hvsall; intros Hvs.
  assert(Hdescpage : In phypage (getMappedPages descParent s)).
  { intuition.
    subst.
    assert(Hpde : partitionDescriptorEntry s).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      intuition. } 
    unfold partitionDescriptorEntry in *.
    assert(Hentrypd: exists entry , nextEntryIsPP descParent PDidx entry s /\ entry <> defaultPage).
    apply Hpde;trivial.
    left;trivial.
    destruct Hentrypd as (pdParent & Hpp & Hnotnul).
    apply inGetMappedPagesGetTableRoot with va pt pdParent ;trivial.
}

apply Hvs in Hdescpage.
clear Hvs.
unfold getMappedPages in *.
assert(HpdAncestor : nextEntryIsPP ancestor PDidx pdAncestor s) by intuition.
rewrite nextEntryIsPPgetPd in *.
rewrite HpdAncestor in *.
unfold getMappedPagesAux in *.
apply filterOptionInIff in Hdescpage.
unfold getMappedPagesOption in *.
apply in_map_iff in Hdescpage.
destruct Hdescpage as (newVA & Hmapped & Hinvas).
unfold getMappedPage in Hmapped.
assert(Hlevel : Some L = StateLib.getNbLevel) by intuition.
rewrite <- Hlevel in *.
case_eq(getIndirection pdAncestor newVA L (nbLevel - 1) s);[intros ptAncestor HptAncestor |
intros HptAncestor];rewrite HptAncestor in *;try now contradict Hmapped.
case_eq(defaultPage =? ptAncestor);intros Hb;rewrite Hb in *;try now contradict Hmapped.
case_eq(StateLib.readPresent ptAncestor (StateLib.getIndexOfAddr newVA fstLevel) (memory s));
[intros present Hpresent |
intros Hpresent];rewrite Hpresent in *;try now contradict Hmapped.

destruct present; try now contradict Hmapped. 
assert(vaInAncestor = newVA).
{ destruct H as (((((Ha & Hk )& Hi ) & Hj ) & Hl ) & Hm).
  intuition.
  clear IHn.
  subst.
  apply eqMappedPagesEqVaddrs with phypage pdAncestor s;trivial.
  apply getMappedPageGetTableRoot with ptvaInAncestor ancestor;trivial.
  rewrite nextEntryIsPPgetPd in *;trivial.
  apply AllVAddrAll.
  apply getMappedPageGetIndirection with ancestor ptAncestor L;trivial.
    rewrite nextEntryIsPPgetPd in *;trivial.
  assert (Hnodupmapped : noDupMappedPagesList s).
  unfold consistency in *;intuition.
  unfold noDupMappedPagesList in *.
  assert(Hnewnodup : NoDup (getMappedPages ancestor s)).
  apply Hnodupmapped;trivial.
  unfold getMappedPages in Hnewnodup.
  rewrite HpdAncestor in *.
  unfold getMappedPagesAux  in *.
  assumption. }
instantiate(1:= phypage).
instantiate (1:= StateLib.getIndexOfAddr vaInAncestor fstLevel).
instantiate (1:= ptvaInAncestor).

  split.
 intuition.
 split.
 assert(Hisancestor : isAncestor currentPart descParent s) by intuition.
 rewrite nextEntryIsPPgetParent in *.

apply isAncestorTrans with descParent;trivial.
intuition.
 intuition.
 subst;trivial.
   subst;trivial.
  subst;trivial.
 

(** setAccessible failed **)
 intros.
  eapply weaken.
  eapply WP.ret.
  intros.
  simpl. intuition.
Admitted.
