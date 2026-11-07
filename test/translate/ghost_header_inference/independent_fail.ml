type 'a owner = { cell : 'a Atomic.t }

let independent left right = (Atomic.get left, Atomic.get right)
(*@ result = independent [owner : 'a owner] left right
    requires left == owner.cell && right == owner.cell
    requires own left value
    ensures own left value *)
