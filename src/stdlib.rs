/* Copyright (c) Meta Platforms, Inc. and affiliates. All rights reserved.
 *
 * This source code is licensed under the Apache 2.0 license found in
 * the LICENSE file in the root directory of this source tree.
 */

use crate::environment::CallLocality;
use crate::environment::CallLocality::*;
use crate::environment::Determinism;
use crate::environment::Determinism::*;
use crate::environment::GuardContext;
use crate::environment::GuardContext::*;
use crate::types::TypeApproximation::*;
use crate::types::*;

// rustfmt likes to split many of these tuples onto many lines, which makes this file unreadable imo.
#[rustfmt::skip]
pub const ERLANG_FUNCTIONS: &[(
    &'static str,
    Determinism,
    GuardContext,
    CallLocality,
    TypeApproximation,
    &[TypeApproximation],
)] = &[
    ("abs", DeterministicOnly, InGuard, Local, Float, &[Float]),
    ("abs", DeterministicOnly, InGuard, Local, Integer, &[Integer]),
    ("adler32", DeterministicOnly, NotInGuard, Remote, Integer, &[List]), // actually iodata
    ("adler32", DeterministicOnly, NotInGuard, Remote, Integer, &[Integer, List]), // List is actually iodata
    ("adler32_combine", DeterministicOnly, NotInGuard, Remote, Integer, &[Integer, Integer, Integer]),
    ("alias", AnyDeterminism, NotInGuard, Local, Ref, &[]),
    // ("alias", AnyDeterminism, NotInGuard, Local, Reference, &[List]),
    ("append_element", DeterministicOnly, NotInGuard, Remote, Tuple, &[Tuple, Any]),
    // ("apply", DeterministicOnly, NotInGuard, Local, Any, &[Fun, Any]),
    // ("apply", DeterministicOnly, NotInGuard, Local, Any, &[Atom, Atom, Any]),
    ("atom_to_binary", DeterministicOnly, NotInGuard, Local, Bitstring, &[Atom]),
    // ("atom_to_binary", DeterministicOnly, NotInGuard, Local, Bitstring, &[Atom, Atom]),
    ("atom_to_list", DeterministicOnly, NotInGuard, Local, List, &[Atom]),
    // ("binary_part", DeterministicOnly, InGuard, Local, Bitstring, &[Bitstring, Tuple]),
    ("binary_part", DeterministicOnly, InGuard, Local, Bitstring, &[Bitstring, Integer, Integer]),
    ("binary_to_atom", DeterministicOnly, NotInGuard, Local, Atom, &[Bitstring]),
    // ("binary_to_atom", DeterministicOnly, NotInGuard, Local, Atom, &[Bitstring, Atom]),
    ("binary_to_existing_atom", AnyDeterminism, NotInGuard, Local, Atom, &[Bitstring]),
    // ("binary_to_existing_atom", DeterministicOnly, NotInGuard, Local, Atom, &[Bitstring, Atom]),
    ("binary_to_float", DeterministicOnly, NotInGuard, Local, Float, &[Bitstring]),
    ("binary_to_integer", DeterministicOnly, NotInGuard, Local, Integer, &[Bitstring]),
    ("binary_to_integer", DeterministicOnly, NotInGuard, Local, Atom, &[Bitstring, Integer]),
    ("binary_to_list", DeterministicOnly, NotInGuard, Local, List, &[Bitstring]),
    ("binary_to_list", DeterministicOnly, NotInGuard, Local, List, &[Bitstring, Integer, Integer]),
    ("binary_to_term", DeterministicOnly, NotInGuard, Local, Any, &[Bitstring]),
    // ("binary_to_term", DeterministicOnly, NotInGuard, Local, Any, &[Bitstring, List]),
    ("bit_size", DeterministicOnly, NotInGuard, Local, Integer, &[Bitstring]),
    ("bitstring_to_list", DeterministicOnly, NotInGuard, Local, List, &[Bitstring]),
    ("bump_reductions", DeterministicOnly, NotInGuard, Remote, Boolean, &[Integer]),
    ("byte_size", DeterministicOnly, InGuard, Local, Integer, &[Bitstring]),
    // cancel_timer
    ("ceil", DeterministicOnly, InGuard, Local, Integer, &[Number]),
    // check_old_code, check_process_code, convert_time_unit, crc32, crc32_combine
    ("date", AnyDeterminism, NotInGuard, Local, Tuple, &[]), // {Integer, Integer, Integer}
    // decode_packet: ridiculously complex, would need a dedicated fuzzer !
    ("delete_element", DeterministicOnly, NotInGuard, Remote, Tuple, &[Tuple, Integer]),
    ("delete_module", DeterministicOnly, NotInGuard, Local, Atom, &[Atom]), // return undefined | true
    // demonitor, disconnect_node, display_term, dist_ctrl_..., 
    ("element", DeterministicOnly, InGuard, Local, Any, &[Tuple, Integer]),
    ("erase", AnyDeterminism, NotInGuard, Local, List, &[]), // [{Any, Any}]
    ("erase", DeterministicOnly, NotInGuard, Local, Any, &[Any]), // Value | undefined
    // error, exit
    ("external_size", AnyDeterminism, NotInGuard, Remote, Integer, &[Any]),
    // ("external_size", DeterministicOnly, NotInGuard, Remote, Integer, &[Any, List]),
    ("float", DeterministicOnly, InGuard, Local, Float, &[Number]),
    ("float_to_binary", DeterministicOnly, NotInGuard, Local, Bitstring, &[Float]),
    // ("float_to_binary", DeterministicOnly, NotInGuard, Local, Bitstring, &[Float, List]),
    ("float_to_list", DeterministicOnly, NotInGuard, Local, List, &[Float]),
    // ("float_to_list", DeterministicOnly, NotInGuard, Local, List, &[Float, List]),
    ("floor", DeterministicOnly, InGuard, Local, Integer, &[Number]),
    ("fun_info", AnyDeterminism, NotInGuard, Remote, List, &[Fun]),
    // ("fun_info", AnyDeterminism, NotInGuard, Remote, Tuple, &[Fun, Any]),
    ("fun_to_list", AnyDeterminism, NotInGuard, Remote, List, &[Fun]),
    ("function_exported", DeterministicOnly, NotInGuard, Remote, Boolean, &[Atom, Atom, Integer]), // M, F, A
    ("garbage_collect", DeterministicOnly, NotInGuard, Local, Boolean, &[]), // true
    ("garbage_collect", DeterministicOnly, NotInGuard, Local, Boolean, &[Pid]), // true
    // ("garbage_collect", DeterministicOnly, NotInGuard, Local, Boolean, &[Pid, List]),
    ("get", AnyDeterminism, NotInGuard, Local, List, &[]),   // [{Any, Any}]
    ("get", AnyDeterminism, NotInGuard, Local, Any, &[Any]),
    ("get_cookie", DeterministicOnly, NotInGuard, Remote, Atom, &[]),
    // ("get_cookie", DeterministicOnly, NotInGuard, Remote, Atom, &[Node]),
    ("get_keys", AnyDeterminism, NotInGuard, Local, List, &[]),
    ("get_keys", AnyDeterminism, NotInGuard, Local, List, &[Any]),
    ("group_leader", AnyDeterminism, NotInGuard, Local, Pid, &[]),
    ("group_leader", DeterministicOnly, NotInGuard, Local, Boolean, &[Pid, Pid]),
    // "halt", we're not interested in stopping the VM during test
    ("hd", DeterministicOnly, InGuard, Local, Any, &[List]),
    // hibernate
    ("insert_element", DeterministicOnly, NotInGuard, Remote, Tuple, &[Integer, Tuple, Any]),
    ("integer_to_binary", DeterministicOnly, NotInGuard, Remote, Bitstring, &[Integer]),
    ("integer_to_binary", DeterministicOnly, NotInGuard, Remote, Bitstring, &[Integer, Integer]),
    ("integer_to_list", DeterministicOnly, NotInGuard, Remote, List, &[Integer]),
    ("integer_to_list", DeterministicOnly, NotInGuard, Remote, List, &[Integer, Integer]),
    ("iolist_size", DeterministicOnly, NotInGuard, Local, Integer, &[List]),
    ("iolist_to_binary", DeterministicOnly, NotInGuard, Local, Bitstring, &[List]),
    ("iolist_to_iovec", DeterministicOnly, NotInGuard, Remote, Bitstring, &[List]),
    ("is_alive", AnyDeterminism, NotInGuard, Local, Boolean, &[]),
    ("is_atom", DeterministicOnly, InGuard, Local, Boolean, &[Any]),
    ("is_binary", DeterministicOnly, InGuard, Local, Boolean, &[Any]),
    ("is_bitstring", DeterministicOnly, InGuard, Local, Boolean, &[Any]),
    ("is_boolean", DeterministicOnly, InGuard, Local, Boolean, &[Any]),
    // is_builtin
    ("is_float", DeterministicOnly, InGuard, Local, Boolean, &[Any]),
    ("is_function", DeterministicOnly, InGuard, Local, Boolean, &[Any]),
    ("is_function", DeterministicOnly, InGuard, Local, Boolean, &[Any, Integer]),
    ("is_integer", DeterministicOnly, InGuard, Local, Boolean, &[Any]),
    ("is_list", DeterministicOnly, InGuard, Local, Boolean, &[Any]),
    ("is_map", DeterministicOnly, InGuard, Local, Boolean, &[Any]),
    ("is_map_key", DeterministicOnly, InGuard, Local, Boolean, &[Any, Map]),
    ("is_number", DeterministicOnly, InGuard, Local, Boolean, &[Any]),
    ("is_pid", DeterministicOnly, InGuard, Local, Boolean, &[Any]),
    ("is_port", DeterministicOnly, InGuard, Local, Boolean, &[Any]),
    ("is_process_alive", AnyDeterminism, NotInGuard, Local, Boolean, &[Pid]),
    // These two are rejected by the compiler if the record name is a literal that does not match any record.
    // ("is_record", AnyDeterminism, NotInGuard, Local, Boolean, &[Any, Atom]),
    // ("is_record", AnyDeterminism, NotInGuard, Local, Boolean, &[Any, Atom, Integer]),
    ("is_reference", DeterministicOnly, InGuard, Local, Boolean, &[Any]),
    ("is_tuple", DeterministicOnly, InGuard, Local, Boolean, &[Any]),
    ("length", DeterministicOnly, InGuard, Local, Integer, &[List]),
    // link
    ("list_to_atom", DeterministicOnly, NotInGuard, Local, Atom, &[List]),
    ("list_to_binary", DeterministicOnly, NotInGuard, Local, Bitstring, &[List]),
    ("list_to_bitstring", DeterministicOnly, NotInGuard, Local, Bitstring, &[List]),
    // list_to_existing_atom, list_to_float/integer/pid/port/ref/tuple, load_module, load_nif
    ("loaded", AnyDeterminism, NotInGuard, Remote, List, &[]),
    ("localtime", AnyDeterminism, NotInGuard, Remote, Tuple, &[]),
    // localtime_to_universaltime
    ("make_ref", AnyDeterminism, NotInGuard, Local, Ref, &[]),
    ("make_tuple", DeterministicOnly, NotInGuard, Remote, Tuple, &[Integer, Any]),
    // make_tuple/3, map_get
    ("map_size", DeterministicOnly, InGuard, Local, Integer, &[Map]),
    // match_spec_test
    ("max", DeterministicOnly, InGuard, Local, Any, &[Any, Any]),
    ("md5", DeterministicOnly, NotInGuard, Remote, Bitstring, &[Bitstring]), // actually takes an iolist
    // various incremental md5 functions
    ("memory", AnyDeterminism, NotInGuard, Remote, List, &[]),
    // memory/1
    ("min", DeterministicOnly, InGuard, Local, Any, &[Any, Any]),
    // module_loaded, monitor, monitor_node
    ("monotonic_time", AnyDeterminism, NotInGuard, Remote, Integer, &[]),
    // monotonic_time/1, nif_error
    ("node", DeterministicOnly, InGuard, Local, Atom, &[]),
    ("node", DeterministicOnly, InGuard, Local, Atom, &[Pid]),
    ("node", DeterministicOnly, InGuard, Local, Atom, &[Port]),
    ("node", DeterministicOnly, InGuard, Local, Atom, &[Ref]),
    ("nodes", AnyDeterminism, NotInGuard, Local, List, &[]), // [atom()]
    // nodes/1, nodes/2
    ("now", AnyDeterminism, NotInGuard, Local, Tuple, &[]),  // {integer(), integer(), integer()}
    // open_port, phash
    ("phash2", AnyDeterminism, NotInGuard, Remote, Integer, &[Any]),
    ("phash2", AnyDeterminism, NotInGuard, Remote, Integer, &[Any, Integer]),
    ("pid_to_list", AnyDeterminism, NotInGuard, Local, List, &[Pid]),
    // port_call, port_command, port_close, port_connect, port_info
    ("port_to_list", AnyDeterminism, NotInGuard, Local, List, &[Port]),
    ("ports", AnyDeterminism, NotInGuard, Remote, List, &[]),
    ("pre_loaded", AnyDeterminism, NotInGuard, Local, List, &[]), // [atom()]
    // process_display, process_flag
    ("process_info", AnyDeterminism, NotInGuard, Local, List, &[Pid]),
    // process_info/2
    ("processes", AnyDeterminism, NotInGuard, Local, List, &[]), // [pid()]
    // purge_module
    ("put", DeterministicOnly, NotInGuard, Local, Any, &[Any, Any]),
    // raise, read_timer,
    ("ref_to_list", AnyDeterminism, NotInGuard, Local, List, &[Ref]),
    ("register", DeterministicOnly, NotInGuard, Local, Boolean, &[Atom, Port]),
    ("register", DeterministicOnly, NotInGuard, Local, Boolean, &[Atom, Pid]),
    ("registered", AnyDeterminism, NotInGuard, Local, List, &[]), // [atom()]
    // resume_process
    ("round", DeterministicOnly, InGuard, Local, Integer, &[Number]),
    // send/2, send/3, send_after, send_nosuspend
    ("self", AnyDeterminism, InGuard, Local, Pid, &[]),
    ("set_cookie", DeterministicOnly, NotInGuard, Remote, Boolean, &[Atom]),
    // set_cookie/2
    ("setelement", DeterministicOnly, NotInGuard, Local, Tuple, &[Integer, Tuple, Any]),
    ("size", DeterministicOnly, NotInGuard, Local, Integer, &[Tuple]),
    ("size", DeterministicOnly, NotInGuard, Local, Integer, &[List]),
    // spawn, spawn_link, spawn_monitor, spawn_opt, spawn_request, spawn_request_abandon
    ("split_binary", DeterministicOnly, NotInGuard, Local, Tuple, &[Bitstring, Integer]),
    // start_timer, statistics, suspend_process, system_flag, system_info, system_monitor, system_profile
    ("term_to_binary", AnyDeterminism, NotInGuard, Local, Bitstring, &[Any]),
    ("term_to_iovec", AnyDeterminism, NotInGuard, Local, List, &[Any]),
    // term_to_binary/2, term_to_iovec/2
    ("throw", DeterministicOnly, NotInGuard, Local, Any, &[Any]), // TODO: get cleaner handling of Bottom vs Any
    ("time", AnyDeterminism, NotInGuard, Local, Tuple, &[]), // {integer, integer, integer}
    ("time_offset", AnyDeterminism, NotInGuard, Remote, Integer, &[]),
    // time_offset/1
    ("timestamp", AnyDeterminism, NotInGuard, Remote, Tuple, &[]),
    ("tl", DeterministicOnly, InGuard, Local, Any, &[List]),
    // trace, trace_delivered, trace_info, trace_pattern
    ("trunc", DeterministicOnly, InGuard, Local, Integer, &[Number]),
    ("tuple_size", DeterministicOnly, InGuard, Local, Integer, &[Tuple]),
    ("tuple_to_list", DeterministicOnly, NotInGuard, Local, List, &[Tuple]),
    // unalias
    ("unique_integer", AnyDeterminism, NotInGuard, Remote, Integer, &[]),
    // unique_integer/1
    ("universaltime", AnyDeterminism, NotInGuard, Remote, Tuple, &[]),
    // universaltime_to_localtime, unlink, 
    ("whereis", AnyDeterminism, NotInGuard, Local, Any, &[Atom]),
    ("yield", DeterministicOnly, NotInGuard, Remote, Boolean, &[]),
];
