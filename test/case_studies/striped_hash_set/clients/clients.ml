let exercise () =
  let set = Striped_hash_set.create 2 in
  assert (not (Striped_hash_set.contains set 1));
  assert (Striped_hash_set.add set 1);
  assert (not (Striped_hash_set.add set 1));
  assert (Striped_hash_set.add set 3);
  assert (Striped_hash_set.add set 2);
  Striped_hash_set.resize set 1;
  assert (Striped_hash_set.contains set 1);
  assert (Striped_hash_set.contains set 3);
  assert (Striped_hash_set.contains set 2);
  Striped_hash_set.resize set 1;
  Striped_hash_set.resize set 2;
  assert (Striped_hash_set.contains set 1);
  assert (Striped_hash_set.contains set 3);
  assert (Striped_hash_set.contains set 2);
  assert (Striped_hash_set.remove set 1);
  assert (not (Striped_hash_set.contains set 1));
  assert (Striped_hash_set.contains set 3);
  assert (Striped_hash_set.contains set 2);
  assert (not (Striped_hash_set.remove set 1));
  assert (Striped_hash_set.remove set 3);
  assert (Striped_hash_set.remove set 2);
  assert (not (Striped_hash_set.contains set 2))

let empty_and_single_stripe () =
  let set = Striped_hash_set.create 1 in
  Striped_hash_set.resize set 1;
  assert (not (Striped_hash_set.contains set 0));
  assert (Striped_hash_set.add set 0);
  Striped_hash_set.resize set 2;
  assert (Striped_hash_set.contains set 0);
  assert (Striped_hash_set.remove set 0);
  Striped_hash_set.resize set 4;
  Striped_hash_set.resize set 9007199254740992;
  assert (not (Striped_hash_set.contains set 0))
