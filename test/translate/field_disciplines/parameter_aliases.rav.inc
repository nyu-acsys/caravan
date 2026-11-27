module Payload: Ocaml_Value_1 {
  rep type Carrier = Int
  func unrestricted() returns (result: Bool) { true }
  func holds(value: Carrier) returns (result: Bool) { true }
}

module ThroughLeft: Caravan_Mutex_Execution_1.FrozenSignature =
  Caravan_Mutex_Execution_1.Frozen[
    Checked_left_X.FrozenTag_2_1_t5_value_1, Payload]
module ThroughAlias: Caravan_Mutex_Execution_1.FrozenSignature =
  Caravan_Mutex_Execution_1.Frozen[
    Checked_same_X.FrozenTag_2_1_t5_value_1, Payload]
module ThroughForward: Caravan_Mutex_Execution_1.FrozenSignature =
  Caravan_Mutex_Execution_1.Frozen[
    Forwarded_worker.Checked_forward_Inner_X.FrozenTag_2_1_t5_value_1, Payload]
module ThroughOther: Caravan_Mutex_Execution_1.FrozenSignature =
  Caravan_Mutex_Execution_1.Frozen[
    Checked_right_X.FrozenTag_2_1_t5_value_1, Payload]

lemma alias_preserves_ownership(location: Ref, value: Int, owner: Ref)
  requires ThroughLeft.ownership(location, value, 1.0, owner)
  ensures ThroughAlias.ownership(location, value, 1.0, owner)
{}

lemma composition_preserves_ownership(location: Ref, value: Int, owner: Ref)
  requires ThroughLeft.ownership(location, value, 1.0, owner)
  ensures ThroughForward.ownership(location, value, 1.0, owner)
{}

module ThroughSecond: Caravan_Mutex_Execution_1.FrozenSignature =
  Caravan_Mutex_Execution_1.Frozen[
    Second_worker.Checked_both_Inner_X.FrozenTag_2_1_t5_value_1, Payload]

lemma second_parameter_preserves_ownership(location: Ref, value: Int, owner: Ref)
  requires ThroughOther.ownership(location, value, 1.0, owner)
  ensures ThroughSecond.ownership(location, value, 1.0, owner)
{}
