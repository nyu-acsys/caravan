let read cell = Attribute_reader.read cell
(*@ result = read cell
    requires Attribute_reader.live cell
    ensures Attribute_reader.live cell *)
