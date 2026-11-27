let integers () =
  let set = Instances.Integer_set.create 2 in
  assert (Instances.Integer_set.add set (-7));
  assert (Instances.Integer_set.add set 7);
  assert (Instances.Integer_set.add set 0);
  assert (not (Instances.Integer_set.add set (-7)));
  Instances.Integer_set.resize set 1;
  assert (Instances.Integer_set.contains set (-7));
  assert (Instances.Integer_set.contains set 7);
  assert (Instances.Integer_set.remove set (-7));
  assert (not (Instances.Integer_set.contains set (-7)));
  assert (Instances.Integer_set.contains set 7);
  Instances.Integer_set.resize set 2;
  assert (Instances.Integer_set.contains set 0)

let records () =
  let set = Instances.Record_set.create 2 in
  let first = { Instances.Record_key.number = 1; flag = true } in
  let equal_first = { Instances.Record_key.number = 1; flag = true } in
  let second = { Instances.Record_key.number = 1; flag = false } in
  assert (Instances.Record_set.add set first);
  assert (not (Instances.Record_set.add set equal_first));
  assert (Instances.Record_set.add set second);
  Instances.Record_set.resize set 1;
  assert (Instances.Record_set.contains set equal_first);
  assert (Instances.Record_set.remove set equal_first);
  assert (not (Instances.Record_set.contains set first));
  assert (Instances.Record_set.contains set second)

let references () =
  let set = Instances.Reference_set.create 2 in
  let first = ref 1 in
  let second = ref 1 in
  assert (Instances.Reference_set.add set first);
  assert (Instances.Reference_set.add set second);
  first := 2;
  Instances.Reference_set.resize set 1;
  assert (Instances.Reference_set.contains set first);
  assert (Instances.Reference_set.remove set first);
  assert (Instances.Reference_set.contains set second)
