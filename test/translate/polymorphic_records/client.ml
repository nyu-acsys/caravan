let client () =
  let first = Api.make 17 in
  Api.write first 42;
  assert (Api.read first = 42);
  let second = Api.make false in
  Api.write second true;
  assert (Api.read second)
