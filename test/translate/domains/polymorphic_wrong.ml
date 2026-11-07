let work value = value
(*@ result = work value ensures result === value *)

let wrong (domain : int Domain.t) = domain
(*@ result = wrong domain
    requires Job.handle domain true
    ensures Job.handle result true *)
