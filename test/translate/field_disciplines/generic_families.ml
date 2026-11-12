type 'a box = { mutable value : 'a [@caravan.frozen] }
type 'a alias = 'a box
