module Worker () = struct
  let work (value : 'a) = value
  (*@ Ghost.returns (fun result () -> result) *)
  (*@ manual *)
  (*@ result, [seen : 'a] = work [expected : 'a] value
      requires expected === value
      ensures result === seen && seen === expected *)

  let run value =
    let domain =
      Domain.spawn (fun () -> work value)
      (*@ Ghost.scope (fun invoke ->
          let domain = invoke value in
          domain) *)
    in
    Domain.join domain
  (*@ Ghost.scope (fun invoke ->
        let (result, seen) = invoke () in
        assert (result === seen && seen === value);
        result) *)
  (*@ manual *)
  (*@ result = run value ensures result === value *)
end

module First = Worker ()
module Second = Worker ()

let client () =
  let number = First.run 7 in
  let flag = Second.run true in
  assert flag;
  number
(*@ result = client () ensures result === 7 *)
