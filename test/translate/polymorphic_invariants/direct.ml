type 'a t = 'a Atomic.t

let read q = Atomic.get q
(*@ result = read q requires constant q value ensures result === value *)

let both (integer : int t) (boolean : bool t) = (Atomic.get integer, Atomic.get boolean)
(*@ result = both integer boolean
    requires constant integer 17 && constant boolean true
    ensures result === (17, true) *)
