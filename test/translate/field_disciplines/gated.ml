type fields = { mutable counter : int [@caravan.frozen] }

let read (record : fields) = record.counter
