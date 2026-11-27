type node = Empty | Node of { mutable count : int [@caravan.frozen] }

let erase (node : node) = Empty
(*@ result = erase node
    requires Count.frozen node value
    ensures Count.frozen result value *)
