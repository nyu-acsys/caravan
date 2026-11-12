# Check identity at the declaration, both resource boundaries, and an ordinary call.
function finish() {
    if (selected && !(requires_owner && ensures_owner && calls_owner))
        failed = 1
}
/^proc / {
    finish()
    selected = ($2 ~ /^(caller|checked\^0|caught|generic_call)\(/)
    requires_owner = ensures_owner = calls_owner = 0
    if (selected) {
        seen[$2] = 1
        if (!match($0, /ghost [^: ]+: Ref/)) {
            failed = 1
            next
        }
        owner = substr($0, RSTART + 6, RLENGTH - 11)
    }
}
selected && /requires .*\.visibility_context\(/ {
    requires_owner = index($0, ".visibility_context(" owner ")") > 0
}
selected && /^  ensures [^ ]+\.visibility_context\(/ {
    ensures_owner = index($0, ".visibility_context(" owner ")") > 0
}
selected && /:= .*\(/ {
    if (index($0, ", " owner ")"))
        calls_owner = 1
}
END {
    finish()
    for (member in seen)
        members++
    if (failed || members != 4)
        exit 1
}
