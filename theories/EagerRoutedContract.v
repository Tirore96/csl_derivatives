Require Import CSL.Contract.

Inductive Control : Set :=
 | F : Control
 | S : Control. 

Inductive AnnEventType : Set :=
 | tau : AnnEventType
 | event : EventType -> AnnEventType
 | ann_event : list Control -> EventType -> AnnEventType.

Inductive ERDerive : Contract -> AnnEventType -> Contract -> Prop :=
 | ERSuccess e : ERDerive Success (event e) Failure
 | ERFailure e : ERDerive Failure (event e) Failure
 | EREventS e : ERDerive (Event e) (event e) Success
 | EREventF e e0 (H: e <> e0) : ERDerive (Event e0) (event e) Failure
 | ERPlusL c0 c0' c1 (H: ERDerive c0 tau c0') : ERDerive (c0 _+_ c1) tau (c0' _+_ c1) 
 | ERPlusR c0 c1 c1' (H: ERDerive c1 tau c1') : ERDerive (c0 _+_ c1) tau (c0 _+_ c1') 
 | ERPlusSS : ERDerive (Success _+_ Success) tau Success
 | ERPlusLC d e c0 c0' c1 
           (H: ERDerive c0 (ann_event d e) c0') : ERDerive (c0 _+_ c1) (ann_event (F::d) e) c0'
 | ERPlusRC d e c0 c1 c1' 
           (H: ERDerive c1 (ann_event d e) c1') : ERDerive (c0 _+_ c1) (ann_event (S::d) e) c1'
 | ERSeqStep ae c0 c0' c1 (H: ERDerive c0 ae c0') : ERDerive (c0 _;_ c1) ae (c0' _;_ c1)
 | ERSeqSuc c : ERDerive (Success _;_ c) tau c.