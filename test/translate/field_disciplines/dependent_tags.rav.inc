module EqualityPayload: Ocaml_Value_1 {
  rep type Carrier = Int
  func unrestricted() returns (result: Bool) { true }
  func holds(value: Carrier) returns (result: Bool) { true }
}
module EqualityLeft: Caravan_Mutex_Execution_1.FrozenSignature =
  Caravan_Mutex_Execution_1.Frozen[
    Parameter_0.FrozenTag_2_1_t7_counter_1, EqualityPayload]
module EqualityRight: Caravan_Mutex_Execution_1.FrozenSignature =
  Caravan_Mutex_Execution_1.Frozen[
    Parameter.FrozenTag_2_1_t7_counter_1, EqualityPayload]

lemma generic_ownership_equality(location: Ref, value: Int, owner: Ref)
  requires EqualityLeft.ownership(location, value, 1.0, owner)
  ensures EqualityRight.ownership(location, value, 1.0, owner)
{}
