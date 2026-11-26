let use cell = Cell.peek cell
(*@ result = use cell
    requires Cell.leaf cell
    ensures Cell.leaf cell
    opens {Cell.root cell} *)
