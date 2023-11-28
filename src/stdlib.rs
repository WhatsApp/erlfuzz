/* Copyright (c) Meta Platforms, Inc. and affiliates. All rights reserved.
 *
 * This source code is licensed under the Apache 2.0 license found in
 * the LICENSE file in the root directory of this source tree.
 */

use std::sync::OnceLock;

use crate::environment::CallLocality;
use crate::environment::CallLocality::*;
use crate::environment::Determinism;
use crate::environment::Determinism::*;
use crate::environment::GuardContext;
use crate::environment::GuardContext::*;
use crate::types::TypeApproximation::*;
use crate::types::*;

static ERLANG_FUNCTIONS: OnceLock<
    Vec<(
        &'static str,
        Determinism,
        GuardContext,
        CallLocality,
        TypeApproximation,
        Vec<TypeApproximation>,
    )>,
> = OnceLock::new();

#[rustfmt::skip]
pub fn get_erlang_functions() -> &'static [(
        &'static str,
        Determinism,
        GuardContext,
        CallLocality,
        TypeApproximation,
        Vec<TypeApproximation>,)] {
    ERLANG_FUNCTIONS.get_or_init(|| vec![
    ("abs", DeterministicOnly, InGuard, Local, Float, vec![Float]),
    ("abs", DeterministicOnly, InGuard, Local, Integer, vec![Integer]),
    ("adler32", DeterministicOnly, NotInGuard, Remote, Integer, vec![List(Box::new(Any))]), // actually iodata
    ("adler32", DeterministicOnly, NotInGuard, Remote, Integer, vec![Integer, List(Box::new(Any))]), // List(Box::new(Any)) is actually iodata
    ("adler32_combine", DeterministicOnly, NotInGuard, Remote, Integer, vec![Integer, Integer, Integer]),
    ("alias", AnyDeterminism, NotInGuard, Local, Ref, vec![]),
    // ("alias", AnyDeterminism, NotInGuard, Local, Reference, vec![List]),
    // TODO: better type for append_element
    ("append_element", DeterministicOnly, NotInGuard, Remote, AnyTuple, vec![AnyTuple, Any]),
    // ("apply", DeterministicOnly, NotInGuard, Local, Any, vec![Fun, Any]),
    // ("apply", DeterministicOnly, NotInGuard, Local, Any, vec![Atom, Atom, Any]),
    ("atom_to_binary", DeterministicOnly, NotInGuard, Local, Bitstring, vec![Atom]),
    // ("atom_to_binary", DeterministicOnly, NotInGuard, Local, Bitstring, vec![Atom, Atom]),
    ("atom_to_list", DeterministicOnly, NotInGuard, Local, List(Box::new(Integer)), vec![Atom]),
    // ("binary_part", DeterministicOnly, InGuard, Local, Bitstring, vec![Bitstring, Tuple]),
    ("binary_part", DeterministicOnly, InGuard, Local, Bitstring, vec![Bitstring, Integer, Integer]),
    ("binary_to_atom", DeterministicOnly, NotInGuard, Local, Atom, vec![Bitstring]),
    // ("binary_to_atom", DeterministicOnly, NotInGuard, Local, Atom, vec![Bitstring, Atom]),
    ("binary_to_existing_atom", AnyDeterminism, NotInGuard, Local, Atom, vec![Bitstring]),
    // ("binary_to_existing_atom", DeterministicOnly, NotInGuard, Local, Atom, vec![Bitstring, Atom]),
    ("binary_to_float", DeterministicOnly, NotInGuard, Local, Float, vec![Bitstring]),
    ("binary_to_integer", DeterministicOnly, NotInGuard, Local, Integer, vec![Bitstring]),
    ("binary_to_integer", DeterministicOnly, NotInGuard, Local, Atom, vec![Bitstring, Integer]),
    ("binary_to_list", DeterministicOnly, NotInGuard, Local, List(Box::new(Integer)), vec![Bitstring]),
    ("binary_to_list", DeterministicOnly, NotInGuard, Local, List(Box::new(Integer)), vec![Bitstring, Integer, Integer]),
    ("binary_to_term", DeterministicOnly, NotInGuard, Local, Any, vec![Bitstring]),
    // ("binary_to_term", DeterministicOnly, NotInGuard, Local, Any, vec![Bitstring, List]),
    ("bit_size", DeterministicOnly, NotInGuard, Local, Integer, vec![Bitstring]),
    ("bitstring_to_list", DeterministicOnly, NotInGuard, Local, List(Box::new(Any)), vec![Bitstring]),
    ("bump_reductions", DeterministicOnly, NotInGuard, Remote, Boolean, vec![Integer]),
    ("byte_size", DeterministicOnly, InGuard, Local, Integer, vec![Bitstring]),
    // cancel_timer
    ("ceil", DeterministicOnly, InGuard, Local, Integer, vec![Number]),
    // check_old_code, check_process_code, convert_time_unit, crc32, crc32_combine
    ("date", AnyDeterminism, NotInGuard, Local, Tuple(vec![Integer, Integer, Integer]), vec![]),
    // decode_packet: ridiculously complex, would need a dedicated fuzzer !
    // TODO: better type for delete_element, element
    ("delete_element", DeterministicOnly, NotInGuard, Remote, AnyTuple, vec![AnyTuple, Integer]),
    ("delete_module", DeterministicOnly, NotInGuard, Local, Atom, vec![Atom]), // return undefined | true
    // demonitor, disconnect_node, display_term, dist_ctrl_..., 
    ("element", DeterministicOnly, InGuard, Local, Any, vec![AnyTuple, Integer]),
    ("erase", AnyDeterminism, NotInGuard, Local, List(Box::new(Tuple(vec![Any, Any]))), vec![]),
    ("erase", DeterministicOnly, NotInGuard, Local, Any, vec![Any]), // Value | undefined
    // error, exit
    ("external_size", AnyDeterminism, NotInGuard, Remote, Integer, vec![Any]),
    // ("external_size", DeterministicOnly, NotInGuard, Remote, Integer, vec![Any, List]),
    ("float", DeterministicOnly, InGuard, Local, Float, vec![Number]),
    ("float_to_binary", DeterministicOnly, NotInGuard, Local, Bitstring, vec![Float]),
    // ("float_to_binary", DeterministicOnly, NotInGuard, Local, Bitstring, vec![Float, List]),
    ("float_to_list", DeterministicOnly, NotInGuard, Local, List(Box::new(Integer)), vec![Float]),
    // ("float_to_list", DeterministicOnly, NotInGuard, Local, List, vec![Float, List]),
    ("floor", DeterministicOnly, InGuard, Local, Integer, vec![Number]),
    ("fun_info", AnyDeterminism, NotInGuard, Remote, List(Box::new(Tuple(vec![Any, Any]))), vec![Fun]),
    // ("fun_info", AnyDeterminism, NotInGuard, Remote, Tuple, vec![Fun, Any]),
    ("fun_to_list", AnyDeterminism, NotInGuard, Remote, List(Box::new(Integer)), vec![Fun]),
    ("function_exported", DeterministicOnly, NotInGuard, Remote, Boolean, vec![Atom, Atom, Integer]), // M, F, A
    ("garbage_collect", DeterministicOnly, NotInGuard, Local, Boolean, vec![]), // true
    ("garbage_collect", DeterministicOnly, NotInGuard, Local, Boolean, vec![Pid]), // true
    // ("garbage_collect", DeterministicOnly, NotInGuard, Local, Boolean, vec![Pid, List]),
    ("get", AnyDeterminism, NotInGuard, Local, List(Box::new(Tuple(vec![Any, Any]))), vec![]),   // [{Any, Any}]
    ("get", AnyDeterminism, NotInGuard, Local, Any, vec![Any]),
    ("get_cookie", DeterministicOnly, NotInGuard, Remote, Atom, vec![]),
    // ("get_cookie", DeterministicOnly, NotInGuard, Remote, Atom, vec![Node]),
    ("get_keys", AnyDeterminism, NotInGuard, Local, List(Box::new(Any)), vec![]),
    ("get_keys", AnyDeterminism, NotInGuard, Local, List(Box::new(Any)), vec![Any]),
    ("group_leader", AnyDeterminism, NotInGuard, Local, Pid, vec![]),
    ("group_leader", DeterministicOnly, NotInGuard, Local, Boolean, vec![Pid, Pid]),
    // "halt", we're not interested in stopping the VM during test
    ("hd", DeterministicOnly, InGuard, Local, Any, vec![List(Box::new(Any))]),
    // hibernate
    ("insert_element", DeterministicOnly, NotInGuard, Remote, AnyTuple, vec![Integer, AnyTuple, Any]),
    ("integer_to_binary", DeterministicOnly, NotInGuard, Remote, Bitstring, vec![Integer]),
    ("integer_to_binary", DeterministicOnly, NotInGuard, Remote, Bitstring, vec![Integer, Integer]),
    ("integer_to_list", DeterministicOnly, NotInGuard, Remote, List(Box::new(Integer)), vec![Integer]),
    ("integer_to_list", DeterministicOnly, NotInGuard, Remote, List(Box::new(Integer)), vec![Integer, Integer]),
    ("iolist_size", DeterministicOnly, NotInGuard, Local, Integer, vec![List(Box::new(Any))]),
    ("iolist_to_binary", DeterministicOnly, NotInGuard, Local, Bitstring, vec![List(Box::new(Any))]),
    ("iolist_to_iovec", DeterministicOnly, NotInGuard, Remote, Bitstring, vec![List(Box::new(Any))]),
    ("is_alive", AnyDeterminism, NotInGuard, Local, Boolean, vec![]),
    ("is_atom", DeterministicOnly, InGuard, Local, Boolean, vec![Any]),
    ("is_binary", DeterministicOnly, InGuard, Local, Boolean, vec![Any]),
    ("is_bitstring", DeterministicOnly, InGuard, Local, Boolean, vec![Any]),
    ("is_boolean", DeterministicOnly, InGuard, Local, Boolean, vec![Any]),
    // is_builtin
    ("is_float", DeterministicOnly, InGuard, Local, Boolean, vec![Any]),
    ("is_function", DeterministicOnly, InGuard, Local, Boolean, vec![Any]),
    ("is_function", DeterministicOnly, InGuard, Local, Boolean, vec![Any, Integer]),
    ("is_integer", DeterministicOnly, InGuard, Local, Boolean, vec![Any]),
    ("is_list", DeterministicOnly, InGuard, Local, Boolean, vec![Any]),
    ("is_map", DeterministicOnly, InGuard, Local, Boolean, vec![Any]),
    ("is_map_key", DeterministicOnly, InGuard, Local, Boolean, vec![Any, Map]),
    ("is_number", DeterministicOnly, InGuard, Local, Boolean, vec![Any]),
    ("is_pid", DeterministicOnly, InGuard, Local, Boolean, vec![Any]),
    ("is_port", DeterministicOnly, InGuard, Local, Boolean, vec![Any]),
    ("is_process_alive", AnyDeterminism, NotInGuard, Local, Boolean, vec![Pid]),
    // These two are rejected by the compiler if the record name is a literal that does not match any record.
    // ("is_record", AnyDeterminism, NotInGuard, Local, Boolean, vec![Any, Atom]),
    // ("is_record", AnyDeterminism, NotInGuard, Local, Boolean, vec![Any, Atom, Integer]),
    ("is_reference", DeterministicOnly, InGuard, Local, Boolean, vec![Any]),
    ("is_tuple", DeterministicOnly, InGuard, Local, Boolean, vec![Any]),
    ("length", DeterministicOnly, InGuard, Local, Integer, vec![List(Box::new(Any))]),
    // link
    ("list_to_atom", DeterministicOnly, NotInGuard, Local, Atom, vec![List(Box::new(Integer))]),
    ("list_to_binary", DeterministicOnly, NotInGuard, Local, Bitstring, vec![List(Box::new(Any))]), // IoList
    ("list_to_bitstring", DeterministicOnly, NotInGuard, Local, Bitstring, vec![List(Box::new(Any))]), // IoList, last one may be a bitstring
    // list_to_existing_atom, list_to_float/integer/pid/port/ref/tuple, load_module, load_nif
    ("loaded", AnyDeterminism, NotInGuard, Remote, List(Box::new(Atom)), vec![]),
    ("localtime", AnyDeterminism, NotInGuard, Remote, Tuple(vec![Tuple(vec![Integer, Integer, Integer]), Tuple(vec![Integer, Integer, Integer])]), vec![]),
    // localtime_to_universaltime
    ("make_ref", AnyDeterminism, NotInGuard, Local, Ref, vec![]),
    ("make_tuple", DeterministicOnly, NotInGuard, Remote, AnyTuple, vec![Integer, Any]),
    // make_tuple/3, map_get
    ("map_size", DeterministicOnly, InGuard, Local, Integer, vec![Map]),
    // match_spec_test
    ("max", DeterministicOnly, InGuard, Local, Any, vec![Any, Any]),
    ("md5", DeterministicOnly, NotInGuard, Remote, Bitstring, vec![Bitstring]), // actually takes an iolist
    // various incremental md5 functions
    ("memory", AnyDeterminism, NotInGuard, Remote, List(Box::new(Tuple(vec![Atom, Integer]))), vec![]),
    // memory/1
    ("min", DeterministicOnly, InGuard, Local, Any, vec![Any, Any]),
    // module_loaded, monitor, monitor_node
    ("monotonic_time", AnyDeterminism, NotInGuard, Remote, Integer, vec![]),
    // monotonic_time/1, nif_error
    ("node", DeterministicOnly, InGuard, Local, Atom, vec![]),
    ("node", DeterministicOnly, InGuard, Local, Atom, vec![Pid]),
    ("node", DeterministicOnly, InGuard, Local, Atom, vec![Port]),
    ("node", DeterministicOnly, InGuard, Local, Atom, vec![Ref]),
    ("nodes", AnyDeterminism, NotInGuard, Local, List(Box::new(Atom)), vec![]),
    // nodes/1, nodes/2
    ("now", AnyDeterminism, NotInGuard, Local, Tuple(vec![Integer, Integer, Integer]), vec![]),
    // open_port, phash
    ("phash2", AnyDeterminism, NotInGuard, Remote, Integer, vec![Any]),
    ("phash2", AnyDeterminism, NotInGuard, Remote, Integer, vec![Any, Integer]),
    ("pid_to_list", AnyDeterminism, NotInGuard, Local, List(Box::new(Integer)), vec![Pid]),
    // port_call, port_command, port_close, port_connect, port_info
    ("port_to_list", AnyDeterminism, NotInGuard, Local, List(Box::new(Integer)), vec![Port]),
    ("ports", AnyDeterminism, NotInGuard, Remote, List(Box::new(Port)), vec![]),
    ("pre_loaded", AnyDeterminism, NotInGuard, Local, List(Box::new(Atom)), vec![]),
    // process_display, process_flag
    ("process_info", AnyDeterminism, NotInGuard, Local, List(Box::new(AnyTuple)), vec![Pid]),
    // process_info/2
    ("processes", AnyDeterminism, NotInGuard, Local, List(Box::new(Pid)), vec![]),
    // purge_module
    ("put", DeterministicOnly, NotInGuard, Local, Any, vec![Any, Any]),
    // raise, read_timer,
    ("ref_to_list", AnyDeterminism, NotInGuard, Local, List(Box::new(Integer)), vec![Ref]),
    ("register", DeterministicOnly, NotInGuard, Local, Boolean, vec![Atom, Port]),
    ("register", DeterministicOnly, NotInGuard, Local, Boolean, vec![Atom, Pid]),
    ("registered", AnyDeterminism, NotInGuard, Local, List(Box::new(Atom)), vec![]),
    // resume_process
    ("round", DeterministicOnly, InGuard, Local, Integer, vec![Number]),
    // send/2, send/3, send_after, send_nosuspend
    ("self", AnyDeterminism, InGuard, Local, Pid, vec![]),
    ("set_cookie", DeterministicOnly, NotInGuard, Remote, Boolean, vec![Atom]),
    // set_cookie/2
    ("setelement", DeterministicOnly, NotInGuard, Local, AnyTuple, vec![Integer, AnyTuple, Any]),
    ("size", DeterministicOnly, NotInGuard, Local, Integer, vec![AnyTuple]),
    ("size", DeterministicOnly, NotInGuard, Local, Integer, vec![List(Box::new(Any))]),
    // spawn, spawn_link, spawn_monitor, spawn_opt, spawn_request, spawn_request_abandon
    ("split_binary", DeterministicOnly, NotInGuard, Local, Tuple(vec![Bitstring, Bitstring]), vec![Bitstring, Integer]),
    // start_timer, statistics, suspend_process, system_flag, system_info, system_monitor, system_profile
    ("term_to_binary", AnyDeterminism, NotInGuard, Local, Bitstring, vec![Any]),
    ("term_to_iovec", AnyDeterminism, NotInGuard, Local, List(Box::new(Any)), vec![Any]),
    // term_to_binary/2, term_to_iovec/2
    ("throw", DeterministicOnly, NotInGuard, Local, Any, vec![Any]), // TODO: get cleaner handling of Bottom vs Any
    ("time", AnyDeterminism, NotInGuard, Local, Tuple(vec![Integer, Integer, Integer]), vec![]),
    ("time_offset", AnyDeterminism, NotInGuard, Remote, Integer, vec![]),
    // time_offset/1
    ("timestamp", AnyDeterminism, NotInGuard, Remote, Tuple(vec![Integer, Integer, Integer]), vec![]),
    ("tl", DeterministicOnly, InGuard, Local, Any, vec![List(Box::new(Any))]),
    // trace, trace_delivered, trace_info, trace_pattern
    ("trunc", DeterministicOnly, InGuard, Local, Integer, vec![Number]),
    ("tuple_size", DeterministicOnly, InGuard, Local, Integer, vec![AnyTuple]),
    ("tuple_to_list", DeterministicOnly, NotInGuard, Local, List(Box::new(Any)), vec![AnyTuple]),
    // unalias
    ("unique_integer", AnyDeterminism, NotInGuard, Remote, Integer, vec![]),
    // unique_integer/1
    ("universaltime", AnyDeterminism, NotInGuard, Remote, Tuple(vec![Tuple(vec![Integer, Integer, Integer]), Tuple(vec![Integer, Integer, Integer])]), vec![]),
    // universaltime_to_localtime, unlink, 
    ("whereis", AnyDeterminism, NotInGuard, Local, Any, vec![Atom]),
    ("yield", DeterministicOnly, NotInGuard, Remote, Boolean, vec![]),
    ])
}

static LIST_FUNCTIONS: OnceLock<Vec<(&'static str, TypeApproximation, Vec<TypeApproximation>)>> =
    OnceLock::new();

#[rustfmt::skip]
pub fn get_list_functions() -> &'static [(&'static str, TypeApproximation, Vec<TypeApproximation>)] {
    LIST_FUNCTIONS.get_or_init(|| vec![
        // all, any
        ("append", List(Box::new(Any)), vec![List(Box::new(List(Box::new(Any))))]),
        ("append", List(Box::new(Any)), vec![List(Box::new(Any)), List(Box::new(Any))]),
        // Actual type is [atom() | integer() | float() | string()] -> string()
        ("concat", List(Box::new(Integer)), vec![List(Box::new(Any))]),
        ("delete", List(Box::new(Any)), vec![List(Box::new(Any)), Any]),
        ("droplast", List(Box::new(Any)), vec![List(Box::new(Any))]),
        // dropwhile
        ("duplicate", List(Box::new(Any)), vec![Integer, Any]),
        ("enumerate", List(Box::new(Tuple(vec![Integer, Any]))), vec![List(Box::new(Any))]),
        ("enumerate", List(Box::new(Tuple(vec![Integer, Any]))), vec![List(Box::new(Any)), Integer]),
        ("enumerate", List(Box::new(Tuple(vec![Integer, Any]))), vec![List(Box::new(Any)), Integer, Integer]),
        // filter, filtermap
        ("flatlength", Integer, vec![List(Box::new(Any))]),
        // flatmap
        ("flatten", List(Box::new(Any)), vec![List(Box::new(Any))]),
        ("flatten", List(Box::new(Any)), vec![List(Box::new(Any)), List(Box::new(Any))]),
        // foldl, foldr
        ("join", List(Box::new(Any)), vec![Any, List(Box::new(Any))]),
        // foreach, keydelete, keyfind, keymap, key...
        ("last", Any, vec![List(Box::new(Any))]),
        // map, mapfoldl, mapfoldr
        ("max", Any, vec![List(Box::new(Any))]),
        ("member", Boolean, vec![Any, List(Box::new(Any))]),
        // merge, merge3
        ("min", Any, vec![List(Box::new(Any))]),
        ("nth", Any, vec![Integer, List(Box::new(Any))]),
        ("nthtail", List(Box::new(Any)), vec![Integer, List(Box::new(Any))]),
        // partition
        ("prefix", Boolean, vec![List(Box::new(Any)), List(Box::new(Any))]),
        ("reverse", List(Box::new(Any)), vec![List(Box::new(Any))]),
        ("reverse", List(Box::new(Any)), vec![List(Box::new(Any)), List(Box::new(Any))]),
        // search
        ("seq", List(Box::new(Integer)), vec![Integer, Integer]),
        ("seq", List(Box::new(Integer)), vec![Integer, Integer, Integer]),
        ("sort", List(Box::new(Any)), vec![List(Box::new(Any))]),
        // sort/2
        ("split", Tuple(vec![List(Box::new(Any)), List(Box::new(Any))]), vec![Integer, List(Box::new(Any))]),
        // splitwith
        ("sublist", List(Box::new(Any)), vec![List(Box::new(Any)), Integer]),
        ("sublist", List(Box::new(Any)), vec![List(Box::new(Any)), Integer, Integer]),
        ("substract", List(Box::new(Any)), vec![List(Box::new(Any)), List(Box::new(Any))]),
        ("suffix", Boolean, vec![List(Box::new(Any)), List(Box::new(Any))]),
        ("sum", Number, vec![List(Box::new(Number))]),
        // takewhile, ukeymerge, ukeysort, umerge, umerge3
        ("unzip", Tuple(vec![List(Box::new(Any)), List(Box::new(Any))]), vec![List(Box::new(Tuple(vec![Any, Any])))]),
        ("unzip3", Tuple(vec![List(Box::new(Any)), List(Box::new(Any)), List(Box::new(Any))]), vec![List(Box::new(Tuple(vec![Any, Any, Any])))]),
        ("usort", List(Box::new(Any)), vec![List(Box::new(Any))]),
        // usort/2, zip, zip3, zipwith, zipwith3
        ("uniq", List(Box::new(Any)), vec![List(Box::new(Any))]),
        // uniq/2
    ])
}

static ETS_FUNCTIONS: OnceLock<
    Vec<(
        &'static str,
        Determinism,
        TypeApproximation,
        Vec<TypeApproximation>,
    )>,
> = OnceLock::new();

#[rustfmt::skip]
pub fn get_ets_functions() -> &'static [(&'static str, Determinism, TypeApproximation, Vec<TypeApproximation>)] {
    ETS_FUNCTIONS.get_or_init(|| vec![
        ("all", AnyDeterminism, List(Box::new(ets_table_type())), vec![]),
        ("delete", DeterministicOnly, Boolean, vec![ets_table_type()]),
        ("delete", DeterministicOnly, Boolean, vec![ets_table_type(), Any]),
        ("delete_all_objects", DeterministicOnly, Boolean, vec![ets_table_type()]),
        ("delete_object", DeterministicOnly, Boolean, vec![ets_table_type(), AnyTuple]),
        // file2tab
        ("first", AnyDeterminism, Any, vec![ets_table_type()]),
        // foldl, folr,
        // from_dets
        // fun2ms
        ("give_away", DeterministicOnly, Boolean, vec![ets_table_type(), Pid, Any]),
        // i
        ("info", AnyDeterminism, Any, vec![ets_table_type()]),
        // info/2
        // init_table
        ("insert", DeterministicOnly, Boolean, vec![ets_table_type(), AnyTuple]),
        ("insert", DeterministicOnly, Boolean, vec![ets_table_type(), List(Box::new(AnyTuple))]),
        ("insert_new", DeterministicOnly, Boolean, vec![ets_table_type(), AnyTuple]),
        ("insert_new", DeterministicOnly, Boolean, vec![ets_table_type(), List(Box::new(AnyTuple))]),
        ("is_compiled_ms", DeterministicOnly, Boolean, vec![Any]),
        ("last", AnyDeterminism, Any, vec![ets_table_type()]),
        ("lookup", AnyDeterminism, AnyTuple, vec![ets_table_type(), Any]),
        ("lookup_element", AnyDeterminism, Any, vec![ets_table_type(), Any, Integer]),
        ("lookup_element", AnyDeterminism, Any, vec![ets_table_type(), Any, Integer, Any]),
        // match/1, match/2, match/3, match_delete, match_object, match_spec_compile, match_spec_run
        ("lookup", DeterministicOnly, Boolean, vec![ets_table_type(), Any]),
        ("new", DeterministicOnly, ets_table_type(), vec![Atom, List(Box::new(Bottom))]), // TODO: should not be Nil, but instead a list of options
        ("next", AnyDeterminism, Any, vec![ets_table_type(), Any]),
        ("prev", AnyDeterminism, Any, vec![ets_table_type(), Any]),
        ("rename", DeterministicOnly, Atom, vec![ets_table_type(), Atom]),
        // repair_continuation
        ("safe_fixtable", DeterministicOnly, Boolean, vec![ets_table_type(), Boolean]),
        // select, select_count, select_delete, select_replace, select_reverse
        // setopts
        ("slot", AnyDeterminism, List(Box::new(Any)), vec![ets_table_type(), Integer]),
        // tab2file
        ("tab2list", AnyDeterminism, List(Box::new(AnyTuple)), vec![ets_table_type()]),
        // tabfile_info, table/1, table/2
        ("take", AnyDeterminism, List(Box::new(AnyTuple)), vec![ets_table_type(), Any]),
        // test_ms, to_dets, update_counter
        ("update_element", DeterministicOnly, Boolean, vec![ets_table_type(), Any, Tuple(vec![Integer, Any])]),
        ("update_element", DeterministicOnly, Boolean, vec![ets_table_type(), Any, List(Box::new(Tuple(vec![Integer, Any])))]),
        ("whereis", AnyDeterminism, Pid, vec![ets_table_type()]),
    ])
}
