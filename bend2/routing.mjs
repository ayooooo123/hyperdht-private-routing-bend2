function word_to_u32(w) {
  let x = 0;
  for (let i = 0; w.$ === "WCon"; i++) {
    x |= Number(w.head) << i;
    w = w.tail;
  }
  return x >>> 0;
}

function u32_to_word(x) {
  let w = {$: "WNil"};
  for (let i = 31; i >= 0; i--) {
    w = {$: "WCon", head: ((x >>> i) & 1) === 1, tail: w};
  }
  return w;
}

function cmp_new(a, b) {
  return {$: a < b ? "LT" : a === b ? "EQ" : "GT"};
}

function nat_divmod(a, b) {
  return b === 0 ? {$: "Tuple", fst: 0, snd: a}
    : {$: "Tuple", fst: Math.trunc(a / b), snd: a % b};
}

function nat_chk(n) {
  if (n > 281474976710655) {
    throw "bend: a Nat past the largest immediate 2^48-1";
  }
  return n;
}

function nat_in(n) {
  if (!Number.isInteger(n) || n < 0 || n > 2 ** 53) {
    throw "bend: expected a Nat host number: an integer from 0 to 2^53";
  }
  return n;
}

function f32_show(x) {
  let s = "nan";
  for (let p = 1; x === x && p <= 9 && f32_round(s) !== x; p += 1) {
    s = String(Number(x.toExponential(p - 1)));
  }
  return (Object.is(x, -0) ? "-0" : s).replace("Infinity", "inf");
}

function f32_bits(x) {
  return new Uint32Array(new Float32Array([x]).buffer)[0];
}

function f32_from_bits(u) {
  return new Float32Array(new Uint32Array([u]).buffer)[0];
}

function f32_read(s) {
  const re = /^[\t\n\v\f\r ]*[+-]?((\d+(?:\.\d*)?|\.\d+)(e[+-]?\d+)?|inf(inity)?|nan)$/i;
  const v = f32_round(s.replace(/inf\w*/i, "Infinity"));
  return re.test(s) ? {$: "Some", value: v} : {$: "None"};
}

const f32_round = function f32_round(s) {
  const d = Number(s);
  const a = Math.abs(d);
  const f = Math.fround(a);
  const g = 2 * a - Math.min(f, 2 ** 128);
  if (g === f || Math.fround(g) !== g || g === Infinity) {
    return Math.sign(d) * f;
  }
  let k = 0;
  while (a * 2 ** k % 1 !== 0) {
    k += 1;
  }
  const [, i, r, e] = /(\d*)\.?(\d*)(?:e([+-]?\d+))?$/i.exec(s);
  const n = Number(e ?? 0) - r.length;
  const x = BigInt(i + r) * 2n ** BigInt(k) * 10n ** BigInt(Math.max(n, 0));
  const y = BigInt(a * 2 ** k) * 10n ** BigInt(Math.max(-n, 0));
  return Math.sign(d) * (x === y || x > y !== g > f ? f : g);
};

const char_new = function char_new(c) {
  return c < 55296 || c >= 57344 && c <= 1114111 ? String.fromCodePoint(c) : String.fromCharCode(56320, c >>> 22, c >>> 11 & 2047, c & 2047);
};

function char_len(s, at = 0) {
  return s[at] === "\uDC00" ? 4 : s.codePointAt(at) > 0xFFFF ? 2 : 1;
}

function char_code(s) {
  return s.length < 4 ? s.codePointAt(0)
    : (s.charCodeAt(1) << 22 | s.charCodeAt(2) << 11 | s.charCodeAt(3)) >>> 0;
}

function string_contains(s, p) {
  // A match must start at a Char boundary, not inside a packed U32 code.
  for (let at = 0; at <= s.length; at += char_len(s, at)) {
    if (s.startsWith(p, at)) {
      return true;
    }
  }
  return false;
}

function str_out(s) {
  return s.replace(/\uDC00[^]{3}/gu, "\uFFFD");
}

function str_in(s) {
  return s.replace(/\p{Cs}/gu, "\uFFFD");
}

// Array
// =====

function array_new(d, v) {
  if (d > 31) {
    throw "bend: an array past the deepest block class 31";
  }
  return Array(2 ** d).fill(v);
}

function array_node(a, b) {
  if (a.length !== b.length) {
    throw "bend: runtime fail-stop";
  }
  return a.concat(b);
}

function array_rmw(a, i, f) {
  const at = i % a.length;
  const old = a[at];
  a[at] = f(old);
  return {$: "Tuple", fst: a, snd: old};
}

// Run
// ===

function run_tail(f, x) {
  return {$: "$JMP", f: f.j?.f === f ? f.j : f, x};
}

function run_clo(j) {
  const f = (x) => run_loop(j(x));
  f.j = j;
  j.f = f;
  return f;
}

function run_loop(r) {
  while (r !== null && typeof r === "object" && r.$ === "$JMP") {
    r = r.f(r.x);
  }
  return r;
}

function run_lib(f, n) {
  return (...a) => a.length < n ? run_lib((...b) => f(...a, ...b), n - a.length)
    : run_loop(f(...a));
}

// Effect
// ======

const $0eff = Object.create(null);

function io_eff(k, run) {
  if (arguments.length > 2) {
    throw new Error("bend: " + k + " takes no need: an effect that waits parks itself");
  }
  if (k in $0eff) {
    throw new Error("bend: two effects register " + k);
  }
  $0eff[k] = run;
}
// Program
// =======

function $consume_ticket(_ticket_0) {
  const _token_id_0 = _ticket_0["token_id"];
  const _period_0 = _ticket_0["period"];
  return {$: "Tuple", "fst": _token_id_0, "snd": _period_0};
}

function $DiversityKey_is_eq(_a_0, _b_0) {
  if (_a_0.$ === "DivIPv4") {
    const _pa_0 = _a_0["prefix24"];
    if (_b_0.$ === "DivIPv4") {
      const _pb_0 = _b_0["prefix24"];
      return $Nat_is_eq(_pa_0, _pb_0);
    } else if (_b_0.$ === "DivIPv6") {
      return false;
    } else {
      return false;
    }
  } else if (_a_0.$ === "DivIPv6") {
    const _pa_1 = _a_0["prefix48"];
    if (_b_0.$ === "DivIPv6") {
      const _pb_1 = _b_0["prefix48"];
      return $Nat_is_eq(_pa_1, _pb_1);
    } else if (_b_0.$ === "DivIPv4") {
      return false;
    } else {
      return false;
    }
  } else {
    const _fa_0 = _a_0["family"];
    const _aa_0 = _a_0["addr"];
    const _pta_0 = _a_0["port"];
    if (_b_0.$ === "DivLoopback") {
      const _fb_0 = _b_0["family"];
      const _ab_0 = _b_0["addr"];
      const _ptb_0 = _b_0["port"];
      return $Bool_and(($Nat_is_eq(_fa_0, _fb_0)), ($Bool_and(($Nat_is_eq(_aa_0, _ab_0)), ($Nat_is_eq(_pta_0, _ptb_0)))));
    } else if (_b_0.$ === "DivIPv4") {
      return false;
    } else {
      return false;
    }
  }
}

function $DiversityKey_is_ne(_a_0, _b_0) {
  return $Bool_not(($DiversityKey_is_eq(_a_0, _b_0)));
}

function $classify_ipv4_loopback(_b0_0, _b1_0, _b2_0, _b3_0, _port_0, _allow_loopback_0) {
  if (!_allow_loopback_0) {
    return {$: "None"};
  } else {
    const _x_0 = nat_chk(_b0_0 * 16777216);
    const _x_1 = nat_chk(_b1_0 * 65536);
    const _p1_0 = nat_chk(_x_0 + _x_1);
    const _x_2 = nat_chk(_b2_0 * 256);
    const _p2_0 = nat_chk(_x_2 + _b3_0);
    return {$: "Some", "value": {$: "DivLoopback", "family": 4, "addr": nat_chk(_p1_0 + _p2_0), "port": _port_0}};
  }
}

function $classify_ipv4_unicast(_b0_0, _b1_0, _b2_0, _b3_0, _port_0, _allow_loopback_0, _is_loop_0) {
  if (_is_loop_0) {
    return $classify_ipv4_loopback(_b0_0, _b1_0, _b2_0, _b3_0, _port_0, _allow_loopback_0);
  } else {
    const _x_0 = nat_chk(_b1_0 * 256);
    const _x_1 = nat_chk(_b0_0 * 65536);
    const _x_2 = nat_chk(_x_0 + _b2_0);
    const _prefix24_0 = nat_chk(_x_1 + _x_2);
    return {$: "Some", "value": {$: "DivIPv4", "prefix24": _prefix24_0}};
  }
}

function $classify_ipv4_checked(_b0_0, _b1_0, _b2_0, _b3_0, _port_0, _allow_loopback_0, _valid_0) {
  if (!_valid_0) {
    return {$: "None"};
  } else {
    return $classify_ipv4_unicast(_b0_0, _b1_0, _b2_0, _b3_0, _port_0, _allow_loopback_0, ($Nat_is_eq(_b0_0, 127)));
  }
}

function $classify_ipv4(_b0_0, _b1_0, _b2_0, _b3_0, _port_0, _allow_loopback_0) {
  const _port_ok_0 = ($Bool_and(($Nat_is_gt(_port_0, 0)), ($Nat_is_le(_port_0, 65535))));
  const _octets_ok_0 = ($Bool_and(($Bool_and((_b0_0 < 224), ($Nat_is_le(_b1_0, 255)))), ($Bool_and(($Nat_is_le(_b2_0, 255)), ($Nat_is_le(_b3_0, 255))))));
  const _all_zero_0 = ($Bool_and(($Bool_and(($Nat_is_eq(_b0_0, 0)), ($Nat_is_eq(_b1_0, 0)))), ($Bool_and(($Nat_is_eq(_b2_0, 0)), ($Nat_is_eq(_b3_0, 0))))));
  const _valid_0 = ($Bool_and(_port_ok_0, ($Bool_and(_octets_ok_0, ($Bool_not(_all_zero_0))))));
  return $classify_ipv4_checked(_b0_0, _b1_0, _b2_0, _b3_0, _port_0, _allow_loopback_0, _valid_0);
}

function $Hop_disjoint(_a_0, _b_0) {
  const _id_a_0 = _a_0["peer_id"];
  const _div_a_0 = _a_0["div"];
  const _id_b_0 = _b_0["peer_id"];
  const _div_b_0 = _b_0["div"];
  return $Bool_and(($Nat_is_ne(_id_a_0, _id_b_0)), ($DiversityKey_is_ne(_div_a_0, _div_b_0)));
}

function $pairwise_disjoint4(_s1_0, _s2_0, _entry_0, _guard_0) {
  const _p12_0 = ($Hop_disjoint(_s1_0, _s2_0));
  const _p13_0 = ($Hop_disjoint(_s1_0, _entry_0));
  const _p14_0 = ($Hop_disjoint(_s1_0, _guard_0));
  const _p23_0 = ($Hop_disjoint(_s2_0, _entry_0));
  const _p24_0 = ($Hop_disjoint(_s2_0, _guard_0));
  const _p34_0 = ($Hop_disjoint(_entry_0, _guard_0));
  return $Bool_and(($Bool_and(_p12_0, _p13_0)), ($Bool_and(($Bool_and(_p14_0, _p23_0)), ($Bool_and(_p24_0, _p34_0)))));
}

function $admit_route4_gate(_s1_0, _s2_0, _entry_0, _guard_0, _ok_0) {
  if (!_ok_0) {
    return {$: "None"};
  } else {
    return {$: "Some", "value": {$: "Route4", "s1": _s1_0, "s2": _s2_0, "entry": _entry_0, "guard": _guard_0}};
  }
}

function $admit_route4(_s1_0, _s2_0, _entry_0, _guard_0) {
  return $admit_route4_gate(_s1_0, _s2_0, _entry_0, _guard_0, ($pairwise_disjoint4(_s1_0, _s2_0, _entry_0, _guard_0)));
}

function $GuardSlot_id(_g_0) {
  const _peer_id_0 = _g_0["peer_id"];
  return _peer_id_0;
}

function $PinnedGuardSet_primary_id(_gs_0) {
  const _t_0 = _gs_0["primary"];
  const _peer_id_0 = _t_0["peer_id"];
  return _peer_id_0;
}

function $PinnedGuardSet_first_reachable(_gs_0) {
  const _t_0 = _gs_0["primary"];
  const _id0_0 = _t_0["peer_id"];
  const _t_1 = _t_0["reachable"];
  if (_t_1) {
    return {$: "Some", "value": _id0_0};
  } else {
    const _t_2 = _gs_0["alt1"];
    const _id1_0 = _t_2["peer_id"];
    const _t_3 = _t_2["reachable"];
    if (_t_3) {
      return {$: "Some", "value": _id1_0};
    } else {
      const _t_4 = _gs_0["alt2"];
      const _id2_0 = _t_4["peer_id"];
      const _t_5 = _t_4["reachable"];
      if (_t_5) {
        return {$: "Some", "value": _id2_0};
      } else {
        return {$: "None"};
      }
    }
  }
}

function $GuardSlot_mark_branch(_id_0, _reach_0, _hit_0) {
  if (_hit_0) {
    return {$: "GuardSlot", "peer_id": _id_0, "reachable": false};
  } else {
    return {$: "GuardSlot", "peer_id": _id_0, "reachable": _reach_0};
  }
}

function $GuardSlot_mark_if(_slot_0, _failed_id_0) {
  const _id_0 = _slot_0["peer_id"];
  const _reach_0 = _slot_0["reachable"];
  return $GuardSlot_mark_branch(_id_0, _reach_0, ($Nat_is_eq(_id_0, _failed_id_0)));
}

function $PinnedGuardSet_failed_branch(_p_id_0, _p_reach_0, _alt1_0, _alt2_0, _failed_id_0, _is_primary_0) {
  if (_is_primary_0) {
    return {$: "GuardSet", "primary": _alt1_0, "alt1": _alt2_0, "alt2": {$: "GuardSlot", "peer_id": _p_id_0, "reachable": false}};
  } else {
    return {$: "GuardSet", "primary": {$: "GuardSlot", "peer_id": _p_id_0, "reachable": _p_reach_0}, "alt1": ($GuardSlot_mark_if(_alt1_0, _failed_id_0)), "alt2": ($GuardSlot_mark_if(_alt2_0, _failed_id_0))};
  }
}

function $PinnedGuardSet_failed(_gs_0, _failed_id_0) {
  const _t_0 = _gs_0["primary"];
  const _p_id_0 = _t_0["peer_id"];
  const _p_reach_0 = _t_0["reachable"];
  const _alt1_0 = _gs_0["alt1"];
  const _alt2_0 = _gs_0["alt2"];
  return $PinnedGuardSet_failed_branch(_p_id_0, _p_reach_0, _alt1_0, _alt2_0, _failed_id_0, ($Nat_is_eq(_p_id_0, _failed_id_0)));
}

function $OutboundAction_targets_only(_act_0, _allowed_addr_0) {
  if (_act_0.$ === "ActDropFailClosed") {
    return true;
  } else {
    const _target_addr_0 = _act_0["target_addr"];
    return $Nat_is_eq(_target_addr_0, _allowed_addr_0);
  }
}

function $endpoint_step(_state_0, _event_0) {
  if (_state_0.$ === "EpBootstrapping") {
    return {$: "Tuple", "fst": {$: "EpBootstrapping"}, "snd": {$: "ActDropFailClosed"}};
  } else if (_state_0.$ === "EpPinned") {
    const _g_0 = _state_0["guard_addr"];
    const _t_0 = _state_0["route_ready"];
    if (_t_0) {
      if (_event_0.$ === "EvSendPayload") {
        return {$: "Tuple", "fst": {$: "EpPinned", "guard_addr": _g_0, "route_ready": true}, "snd": {$: "ActSendToPeer", "target_addr": _g_0}};
      } else if (_event_0.$ === "EvRouteFailed") {
        return {$: "Tuple", "fst": {$: "EpPinned", "guard_addr": _g_0, "route_ready": false}, "snd": {$: "ActDropFailClosed"}};
      } else if (_event_0.$ === "EvRouteExpired") {
        return {$: "Tuple", "fst": {$: "EpPinned", "guard_addr": _g_0, "route_ready": false}, "snd": {$: "ActDropFailClosed"}};
      } else if (_event_0.$ === "EvRouteRecovered") {
        return {$: "Tuple", "fst": {$: "EpPinned", "guard_addr": _g_0, "route_ready": true}, "snd": {$: "ActDropFailClosed"}};
      } else if (_event_0.$ === "EvSuspend") {
        return {$: "Tuple", "fst": {$: "EpSuspended", "guard_addr": _g_0}, "snd": {$: "ActDropFailClosed"}};
      } else if (_event_0.$ === "EvResume") {
        return {$: "Tuple", "fst": {$: "EpPinned", "guard_addr": _g_0, "route_ready": true}, "snd": {$: "ActDropFailClosed"}};
      } else {
        return {$: "Tuple", "fst": {$: "EpDestroyed"}, "snd": {$: "ActDropFailClosed"}};
      }
    } else {
      if (_event_0.$ === "EvSendPayload") {
        return {$: "Tuple", "fst": {$: "EpPinned", "guard_addr": _g_0, "route_ready": false}, "snd": {$: "ActDropFailClosed"}};
      } else if (_event_0.$ === "EvRouteFailed") {
        return {$: "Tuple", "fst": {$: "EpPinned", "guard_addr": _g_0, "route_ready": false}, "snd": {$: "ActDropFailClosed"}};
      } else if (_event_0.$ === "EvRouteExpired") {
        return {$: "Tuple", "fst": {$: "EpPinned", "guard_addr": _g_0, "route_ready": false}, "snd": {$: "ActDropFailClosed"}};
      } else if (_event_0.$ === "EvRouteRecovered") {
        return {$: "Tuple", "fst": {$: "EpPinned", "guard_addr": _g_0, "route_ready": true}, "snd": {$: "ActDropFailClosed"}};
      } else if (_event_0.$ === "EvSuspend") {
        return {$: "Tuple", "fst": {$: "EpSuspended", "guard_addr": _g_0}, "snd": {$: "ActDropFailClosed"}};
      } else if (_event_0.$ === "EvResume") {
        return {$: "Tuple", "fst": {$: "EpPinned", "guard_addr": _g_0, "route_ready": false}, "snd": {$: "ActDropFailClosed"}};
      } else {
        return {$: "Tuple", "fst": {$: "EpDestroyed"}, "snd": {$: "ActDropFailClosed"}};
      }
    }
  } else if (_state_0.$ === "EpSuspended") {
    const _g_1 = _state_0["guard_addr"];
    if (_event_0.$ === "EvResume") {
      return {$: "Tuple", "fst": {$: "EpPinned", "guard_addr": _g_1, "route_ready": false}, "snd": {$: "ActDropFailClosed"}};
    } else if (_event_0.$ === "EvDestroy") {
      return {$: "Tuple", "fst": {$: "EpDestroyed"}, "snd": {$: "ActDropFailClosed"}};
    } else {
      return {$: "Tuple", "fst": {$: "EpSuspended", "guard_addr": _g_1}, "snd": {$: "ActDropFailClosed"}};
    }
  } else {
    return {$: "Tuple", "fst": {$: "EpDestroyed"}, "snd": {$: "ActDropFailClosed"}};
  }
}

function $next_descriptor_seq_pick(_base_0, _now_0, _now_gt_0) {
  if (_now_gt_0) {
    return _now_0;
  } else {
    return nat_chk(_base_0 + 1);
  }
}

function $next_descriptor_seq(_prev_seq_0, _remote_seq_0, _now_0) {
  const _base_0 = (_prev_seq_0 > _remote_seq_0 ? _prev_seq_0 : _remote_seq_0);
  return $next_descriptor_seq_pick(_base_0, _now_0, ($Nat_is_gt(_now_0, _base_0)));
}

function $CircuitState_retire(_c_0) {
  const _closed_0 = _c_0["closed"];
  const _last_id_0 = _c_0["last_stream_id"];
  const _streams_0 = _c_0["admitted_streams"];
  return {$: "CircuitState", "closed": _closed_0, "retired": true, "last_stream_id": _last_id_0, "admitted_streams": _streams_0};
}

function $CircuitState_streams(_c_0) {
  const _streams_0 = _c_0["admitted_streams"];
  return _streams_0;
}

function $CircuitState_can_admit(_c_0) {
  const _closed_0 = _c_0["closed"];
  const _retired_0 = _c_0["retired"];
  return $Bool_and(($Bool_not(_closed_0)), ($Bool_not(_retired_0)));
}

function $splice_firewall_allow(_expected_host_0, _expected_port_0, _actual_host_0, _actual_port_0) {
  return $Bool_and(($Nat_is_eq(_expected_host_0, _actual_host_0)), ($Nat_is_eq(_expected_port_0, _actual_port_0)));
}

function $admit_splice_pair(_stream_id_0, _up_udx_id_0, _down_udx_id_0) {
  if (_up_udx_id_0 === 0) {
    return {$: "None"};
  } else {
    const __0 = (_up_udx_id_0 - 1);
    if (_down_udx_id_0 === 0) {
      return {$: "None"};
    } else {
      const _down_p_0 = (_down_udx_id_0 - 1);
      return {$: "Some", "value": {$: "SplicePair", "stream_id": _stream_id_0, "up_udx_id": nat_chk(__0 + 1), "down_udx_id": nat_chk(_down_p_0 + 1)}};
    }
  }
}

function $Nat_is_eq(_a_0, _b_0) {
  return $Cmp_is_eq(cmp_new(_a_0, _b_0));
}

function $Bool_and(_a_0, _b_0) {
  if (!_a_0) {
    return false;
  } else {
    return _b_0;
  }
}

function $Bool_not(_b_0) {
  if (!_b_0) {
    return true;
  } else {
    return false;
  }
}

function $Nat_is_gt(_a_0, _b_0) {
  return $Cmp_is_gt(cmp_new(_a_0, _b_0));
}

function $Nat_is_le(_a_0, _b_0) {
  return $Cmp_is_le(cmp_new(_a_0, _b_0));
}

function $Nat_is_ne(_a_0, _b_0) {
  return $Bool_not(($Cmp_is_eq(cmp_new(_a_0, _b_0))));
}

function $Cmp_is_eq(_c_0) {
  if (_c_0.$ === "EQ") {
    return true;
  } else {
    return false;
  }
}

function $Cmp_is_gt(_c_0) {
  if (_c_0.$ === "GT") {
    return true;
  } else {
    return false;
  }
}

function $Cmp_is_le(_c_0) {
  if (_c_0.$ === "GT") {
    return false;
  } else {
    return true;
  }
}
export default {
  "consume_ticket": run_lib((a0) => run_loop($consume_ticket(a0)), 1),
  "DiversityKey.is_eq": run_lib((a0,a1) => run_loop($DiversityKey_is_eq(a0,a1)), 2),
  "DiversityKey.is_ne": run_lib((a0,a1) => run_loop($DiversityKey_is_ne(a0,a1)), 2),
  "classify_ipv4_loopback": run_lib((a0,a1,a2,a3,a4,a5) => run_loop($classify_ipv4_loopback(nat_in(a0),nat_in(a1),nat_in(a2),nat_in(a3),nat_in(a4),a5)), 6),
  "classify_ipv4_unicast": run_lib((a0,a1,a2,a3,a4,a5,a6) => run_loop($classify_ipv4_unicast(nat_in(a0),nat_in(a1),nat_in(a2),nat_in(a3),nat_in(a4),a5,a6)), 7),
  "classify_ipv4_checked": run_lib((a0,a1,a2,a3,a4,a5,a6) => run_loop($classify_ipv4_checked(nat_in(a0),nat_in(a1),nat_in(a2),nat_in(a3),nat_in(a4),a5,a6)), 7),
  "classify_ipv4": run_lib((a0,a1,a2,a3,a4,a5) => run_loop($classify_ipv4(nat_in(a0),nat_in(a1),nat_in(a2),nat_in(a3),nat_in(a4),a5)), 6),
  "Hop.disjoint": run_lib((a0,a1) => run_loop($Hop_disjoint(a0,a1)), 2),
  "pairwise_disjoint4": run_lib((a0,a1,a2,a3) => run_loop($pairwise_disjoint4(a0,a1,a2,a3)), 4),
  "admit_route4_gate": run_lib((a0,a1,a2,a3,a4) => run_loop($admit_route4_gate(a0,a1,a2,a3,a4)), 5),
  "admit_route4": run_lib((a0,a1,a2,a3) => run_loop($admit_route4(a0,a1,a2,a3)), 4),
  "GuardSlot.id": run_lib((a0) => run_loop($GuardSlot_id(a0)), 1),
  "PinnedGuardSet.primary_id": run_lib((a0) => run_loop($PinnedGuardSet_primary_id(a0)), 1),
  "PinnedGuardSet.first_reachable": run_lib((a0) => run_loop($PinnedGuardSet_first_reachable(a0)), 1),
  "GuardSlot.mark_branch": run_lib((a0,a1,a2) => run_loop($GuardSlot_mark_branch(nat_in(a0),a1,a2)), 3),
  "GuardSlot.mark_if": run_lib((a0,a1) => run_loop($GuardSlot_mark_if(a0,nat_in(a1))), 2),
  "PinnedGuardSet.failed_branch": run_lib((a0,a1,a2,a3,a4,a5) => run_loop($PinnedGuardSet_failed_branch(nat_in(a0),a1,a2,a3,nat_in(a4),a5)), 6),
  "PinnedGuardSet.failed": run_lib((a0,a1) => run_loop($PinnedGuardSet_failed(a0,nat_in(a1))), 2),
  "OutboundAction.targets_only": run_lib((a0,a1) => run_loop($OutboundAction_targets_only(a0,nat_in(a1))), 2),
  "endpoint_step": run_lib((a0,a1) => run_loop($endpoint_step(a0,a1)), 2),
  "next_descriptor_seq_pick": run_lib((a0,a1,a2) => run_loop($next_descriptor_seq_pick(nat_in(a0),nat_in(a1),a2)), 3),
  "next_descriptor_seq": run_lib((a0,a1,a2) => run_loop($next_descriptor_seq(nat_in(a0),nat_in(a1),nat_in(a2))), 3),
  "CircuitState.retire": run_lib((a0) => run_loop($CircuitState_retire(a0)), 1),
  "CircuitState.streams": run_lib((a0) => run_loop($CircuitState_streams(a0)), 1),
  "CircuitState.can_admit": run_lib((a0) => run_loop($CircuitState_can_admit(a0)), 1),
  "splice_firewall_allow": run_lib((a0,a1,a2,a3) => run_loop($splice_firewall_allow(nat_in(a0),nat_in(a1),nat_in(a2),nat_in(a3))), 4),
  "admit_splice_pair": run_lib((a0,a1,a2) => run_loop($admit_splice_pair(nat_in(a0),nat_in(a1),nat_in(a2))), 3),
};
