let invalid = function [] -> 0 | value :: _ -> value
(*@ result = invalid xs ensures boolean_items xs *)
