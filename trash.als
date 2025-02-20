var sig File {}
var sig Trash in File {}

fact init {
  no Trash
}

pred empty {
  some Trash and       // guard
  after no Trash and   // effect on Trash
  File' = File - Trash // effect on File
}

pred delete [f : File] {
  not (f in Trash)   // guard
  Trash' = Trash + f // effect on Trash
  File' = File       // frame condition on File
}

pred restore [f : File] {
  f in Trash         // guard
  Trash' = Trash - f // effect on Trash
  File' = File       // frame condition on File
}

pred do_something_else {
  File' = File
  Trash' = Trash
}

pred deleteFromTrash [f : File] {
  f in Trash
  Trash' = Trash - f
  File' = File - f
}

pred deleteNotFromTrash [f : File] {
  not (f in Trash)
  Trash' = Trash
  File' = File - f
}

assert restore_after_delete {
  always (all f : File | restore[f] implies once delete[f])
}

check restore_after_delete for 3 but 1.. steps

assert delete_all {
  always ((Trash = File and empty) implies always no File)
}

check delete_all

fact trans {
  always (empty or (some f : File | delete[f] or restore[f]) or do_something_else)
}

run example {}

run no_files {
  some File
  eventually no File
} for 5