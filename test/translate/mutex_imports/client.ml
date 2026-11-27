let roundtrip mutex =
  Lock_api.acquire mutex;
  Lock_api.Nested.release mutex

let fresh () =
  let mutex = Mutex.create () in
  Lock_api.acquire mutex;
  Lock_api.Nested.release mutex
