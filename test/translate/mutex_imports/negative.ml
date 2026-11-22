let duplicate_acquire mutex =
  Lock_api.acquire mutex;
  Lock_api.acquire mutex

let missing_release mutex = Lock_api.acquire mutex
