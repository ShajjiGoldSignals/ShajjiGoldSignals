"""
XAUUSD signal scanner.
Runs on a schedule (GitHub Actions). Pulls live gold price/tick data from the free
xaus.com API, builds 5m/15m/30m/1H candles, checks the full rule set, and sends a
Telegram notification when a BUY/SELL/PRE-SIGNAL fires. State (last signal, to avoid
duplicate alerts) is persisted in state.json and committed back to the repo.
"""

import json
import math
import os
import sys
from datetime import datetime, timezone, timedelta

import requests

# ============================= CONFIG =============================
SYMBOL = "xau"
INTRADAY_HOURS = 48
ATR_PERIOD = 15
RSI_PERIOD = 14
MA_PERIODS = [21, 50, 200]
FAST_MA_PROXIMITY_USD = 5
MIN_BREAK_USD = 5
LINE_DEVIATION_USD = 3
SR_DEVIATION_USD = 5
SWING_LOOKBACK = 5
RISK_REWARD = 1
# session windows in PKT: (start_hour,start_min,end_hour,end_min)
SESSION_WINDOWS = [(7, 0, 16, 0), (20, 0, 23, 0)]

STATE_FILE = os.path.join(os.path.dirname(__file__), "state.json")
TELEGRAM_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN", "")
TELEGRAM_CHAT_ID = os.environ.get("TELEGRAM_CHAT_ID", "")


# ============================= DATA FETCH =============================
def fetch_intraday():
    url = f"https://xaus.com/api/v1/intraday?symbol={SYMBOL}&hours={INTRADAY_HOURS}"
    r = requests.get(url, timeout=20)
    r.raise_for_status()
    return r.json().get("points", [])


def fetch_spot():
    url = "https://xaus.com/api/v1/spot?compact=1"
    r = requests.get(url, timeout=20)
    r.raise_for_status()
    return r.json()


# ============================= CANDLES =============================
def ts_of(point):
    t = point.get("t")
    if isinstance(t, str):
        return datetime.fromisoformat(t.replace("Z", "+00:00")).timestamp() * 1000
    if isinstance(t, (int, float)):
        return t if t > 2e10 else t * 1000
    return datetime.now(timezone.utc).timestamp() * 1000


def build_candles(points, interval_min):
    if not points:
        return []
    pts = sorted(points, key=ts_of)
    bucket_ms = interval_min * 60000
    out = []
    bucket_start = math.floor(ts_of(pts[0]) / bucket_ms) * bucket_ms
    o = h = l = c = None
    cnt = 0

    def push():
        if cnt > 0:
            out.append({"t": bucket_start, "o": o, "h": h, "l": l, "c": c})

    for p in pts:
        ts = ts_of(p)
        price = p.get("p")
        if price is None:
            continue
        bs = math.floor(ts / bucket_ms) * bucket_ms
        if bs != bucket_start:
            push()
            bucket_start, o, h, l, c, cnt = bs, price, price, price, price, 1
        else:
            if o is None:
                o = price
            h = price if h is None else max(h, price)
            l = price if l is None else min(l, price)
            c = price
            cnt += 1
    push()
    return out


# ============================= INDICATORS =============================
def sma(vals, period):
    if len(vals) < period:
        return None
    return sum(vals[-period:]) / period


def rsi_series(closes, period):
    out = [None] * len(closes)
    if len(closes) < period + 1:
        return out
    gains = losses = 0.0
    for i in range(1, period + 1):
        d = closes[i] - closes[i - 1]
        gains += max(d, 0)
        losses += max(-d, 0)
    avg_gain, avg_loss = gains / period, losses / period
    out[period] = 100.0 if avg_loss == 0 else 100 - (100 / (1 + avg_gain / avg_loss))
    for i in range(period + 1, len(closes)):
        d = closes[i] - closes[i - 1]
        g, ls = max(d, 0), max(-d, 0)
        avg_gain = (avg_gain * (period - 1) + g) / period
        avg_loss = (avg_loss * (period - 1) + ls) / period
        out[i] = 100.0 if avg_loss == 0 else 100 - (100 / (1 + avg_gain / avg_loss))
    return out


def atr(candles, period):
    if len(candles) < period + 1:
        return None
    trs = []
    for i in range(1, len(candles)):
        cur, prev = candles[i], candles[i - 1]
        tr = max(cur["h"] - cur["l"], abs(cur["h"] - prev["c"]), abs(cur["l"] - prev["c"]))
        trs.append(tr)
    tail = trs[-period:]
    return sum(tail) / len(tail)


# ============================= SWINGS =============================
def find_swings(candles, lookback):
    highs, lows = [], []
    for i in range(lookback, len(candles) - lookback):
        c = candles[i]
        is_high = all(candles[j]["h"] < c["h"] for j in range(i - lookback, i + lookback + 1) if j != i)
        is_low = all(candles[j]["l"] > c["l"] for j in range(i - lookback, i + lookback + 1) if j != i)
        if is_high:
            highs.append({"i": i, "price": c["h"]})
        if is_low:
            lows.append({"i": i, "price": c["l"]})
    return highs, lows


# ============================= TRENDLINES =============================
def detect_trendline(swings, min_touches, deviation):
    if len(swings) < 3:
        return None
    pts = swings[-12:]
    best = None
    for a in range(len(pts)):
        for b in range(a + 1, len(pts)):
            p1, p2 = pts[a], pts[b]
            if p2["i"] == p1["i"]:
                continue
            slope = (p2["price"] - p1["price"]) / (p2["i"] - p1["i"])
            intercept = p1["price"] - slope * p1["i"]
            touches = sum(1 for p in pts if abs(p["price"] - (slope * p["i"] + intercept)) <= deviation)
            if touches >= min_touches and (best is None or touches > best["touches"]):
                best = {"slope": slope, "intercept": intercept, "touches": touches}
    return best


def line_value_at(line, idx):
    return line["slope"] * idx + line["intercept"]


# ============================= SUPPORT / RESISTANCE (1h) =============================
def detect_sr(candles, deviation):
    highs, lows = find_swings(candles, SWING_LOOKBACK)

    def cluster(points):
        clusters = []
        for p in points:
            found = next((c for c in clusters if abs(c["avg"] - p["price"]) <= deviation), None)
            if found:
                found["pts"].append(p)
                found["avg"] = sum(x["price"] for x in found["pts"]) / len(found["pts"])
            else:
                clusters.append({"avg": p["price"], "pts": [p]})
        return [c for c in clusters if len(c["pts"]) >= 3]

    return cluster(highs), cluster(lows)


# ============================= LINE STRIKE =============================
def detect_line_strike(candles):
    if len(candles) < 4:
        return None, None
    c1, c2, c3, c4 = candles[-4:]
    direction = "up" if c1["c"] > c1["o"] else "down"
    same3 = all((c["c"] > c["o"]) if direction == "up" else (c["c"] < c["o"]) for c in (c1, c2, c3))
    if not same3:
        return None, None
    c4dir = "up" if c4["c"] > c4["o"] else "down"
    if c4dir == direction:
        return None, None
    range_low, range_high = min(c1["l"], c2["l"], c3["l"]), max(c1["h"], c2["h"], c3["h"])
    if (direction == "up" and c4["c"] < range_low) or (direction == "down" and c4["c"] > range_high):
        return "3-line", ("down" if direction == "up" else "up")
    if (direction == "up" and c4["c"] < c3["o"]) or (direction == "down" and c4["c"] > c3["o"]):
        return "2-line", ("down" if direction == "up" else "up")
    return None, None


# ============================= RSI DIVERGENCE =============================
def detect_divergence(candles, rsi_vals):
    highs, lows = find_swings(candles, 3)
    result = {"bullish": None, "bearish": None}

    def rsi_at(i):
        return rsi_vals[i] if i < len(rsi_vals) else None

    if len(highs) >= 2:
        h1, h2 = highs[-2], highs[-1]
        r1, r2 = rsi_at(h1["i"]), rsi_at(h2["i"])
        if r1 is not None and r2 is not None:
            if h2["price"] > h1["price"] and r2 < r1:
                result["bearish"] = "regular"
            elif h2["price"] < h1["price"] and r2 > r1:
                result["bearish"] = "hidden"
    if len(lows) >= 2:
        l1, l2 = lows[-2], lows[-1]
        r1, r2 = rsi_at(l1["i"]), rsi_at(l2["i"])
        if r1 is not None and r2 is not None:
            if l2["price"] < l1["price"] and r2 > r1:
                result["bullish"] = "regular"
            elif l2["price"] > l1["price"] and r2 < r1:
                result["bullish"] = "hidden"
    return result


# ============================= SESSION =============================
def in_session_window(now_utc):
    pkt = now_utc + timedelta(hours=5)
    mins = pkt.hour * 60 + pkt.minute
    for h1, m1, h2, m2 in SESSION_WINDOWS:
        if h1 * 60 + m1 <= mins <= h2 * 60 + m2:
            return True
    return False


# ============================= SIGNAL ENGINE =============================
def evaluate(candles5, candles15, candles30, candles60, now_utc, bypass_session=False):
    if len(candles5) < 60 or len(candles15) < 40 or len(candles30) < 30 or len(candles60) < 20:
        return {"state": "WARMING_UP"}

    price = candles5[-1]["c"]
    closes5 = [c["c"] for c in candles5]
    ma21 = sma(closes5, 21)
    ma50 = sma(closes5, 50)
    ma200 = sma(closes5, min(200, len(closes5)))
    rsi5 = rsi_series(closes5, RSI_PERIOD)
    rsi15 = rsi_series([c["c"] for c in candles15], RSI_PERIOD)
    rsi30 = rsi_series([c["c"] for c in candles30], RSI_PERIOD)
    atr5 = atr(candles5, ATR_PERIOD)

    sw5h, sw5l = find_swings(candles5, SWING_LOOKBACK)
    sw15h, sw15l = find_swings(candles15, SWING_LOOKBACK)
    sw30h, sw30l = find_swings(candles30, SWING_LOOKBACK)

    tl5up, tl5dn = detect_trendline(sw5h, 2, LINE_DEVIATION_USD), detect_trendline(sw5l, 2, LINE_DEVIATION_USD)
    tl15up, tl15dn = detect_trendline(sw15h, 2, LINE_DEVIATION_USD), detect_trendline(sw15l, 2, LINE_DEVIATION_USD)
    tl30up, tl30dn = detect_trendline(sw30h, 2, LINE_DEVIATION_USD), detect_trendline(sw30l, 2, LINE_DEVIATION_USD)

    res_clusters, sup_clusters = detect_sr(candles60, SR_DEVIATION_USD)
    resistances = [c["avg"] for c in res_clusters]
    supports = [c["avg"] for c in sup_clusters]
    nearest_res = min((v for v in resistances if v > price), default=None)
    nearest_sup = max((v for v in supports if v < price), default=None)

    strike_type, strike_rev = detect_line_strike(candles5)
    div5 = detect_divergence(candles5, rsi5)
    div15 = detect_divergence(candles15, rsi15)
    div30 = detect_divergence(candles30, rsi30)

    real_in_session = in_session_window(now_utc)
    in_session = real_in_session or bypass_session
    ma_proximity = ma21 is not None and abs(price - ma21) <= FAST_MA_PROXIMITY_USD

    def eval_side(direction):
        conds = []
        session_label = "Within trading session (7am-4pm or 8pm-11pm PKT)"
        if bypass_session and not real_in_session:
            session_label += " [bypassed for demo run]"
        conds.append(("session", session_label, in_session))
        conds.append(("ma_proximity", f"21MA(5m) within ${FAST_MA_PROXIMITY_USD} of price", ma_proximity))

        relevant = ([("5m", tl5dn, len(candles5)), ("15m", tl15dn, len(candles15)), ("30m", tl30dn, len(candles30))]
                    if direction == "buy" else
                    [("5m", tl5up, len(candles5)), ("15m", tl15up, len(candles15)), ("30m", tl30up, len(candles30))])
        tl_pass, tl_desc = False, "No valid trendline break+retest found"
        for tf, line, last_len in relevant:
            if not line:
                continue
            line_now = line_value_at(line, last_len - 1)
            broke = (price > line_now + MIN_BREAK_USD) if direction == "buy" else (price < line_now - MIN_BREAK_USD)
            if broke:
                tl_pass = True
                tl_desc = f"Trendline break+retest confirmed on {tf} (line ~${line_now:.2f})"
                break
        conds.append(("trendline", tl_desc, tl_pass))

        sr_pass, sr_desc = False, "No 1H support/resistance break+retest found"
        if direction == "buy" and nearest_res is not None and price > nearest_res + MIN_BREAK_USD:
            sr_pass, sr_desc = True, f"1H resistance ~${nearest_res:.2f} broken + retested"
        if direction == "sell" and nearest_sup is not None and price < nearest_sup - MIN_BREAK_USD:
            sr_pass, sr_desc = True, f"1H support ~${nearest_sup:.2f} broken + retested"
        conds.append(("sr", sr_desc, sr_pass))

        want_rev = "up" if direction == "buy" else "down"
        strike_match = strike_type is not None and strike_rev == want_rev
        strike_desc = (f"{'3-line strike' if strike_type=='3-line' else '2-line strike (partial)'} confirms rejection"
                        if strike_match else "No qualifying line-strike rejection yet")
        conds.append(("strike", strike_desc, strike_match))

        want_key = "bullish" if direction == "buy" else "bearish"
        hits = []
        for label, d in (("5m", div5), ("15m", div15), ("30m", div30)):
            if d[want_key]:
                hits.append(f"{label} {d[want_key]}")
        div_desc = f"RSI divergence: {', '.join(hits)}" if hits else "No RSI divergence in trade direction"
        conds.append(("divergence", div_desc, len(hits) > 0))

        passed = sum(1 for _, _, p in conds if p)
        total = len(conds)
        return {
            "dir": direction, "conds": conds, "passed": passed, "total": total,
            "all_pass": passed == total, "nearly_all": passed >= total - 1,
        }

    buy_side, sell_side = eval_side("buy"), eval_side("sell")
    chosen = buy_side if buy_side["passed"] >= sell_side["passed"] else sell_side

    state = "NO_TRADE"
    if in_session:
        if chosen["all_pass"]:
            state = "BUY" if chosen["dir"] == "buy" else "SELL"
        elif chosen["nearly_all"]:
            state = "PRE_BUY" if chosen["dir"] == "buy" else "PRE_SELL"

    entry = sl = tp = None
    if atr5 and state != "NO_TRADE" and state != "WARMING_UP":
        dist = atr5 * 2
        entry = price
        if "BUY" in state:
            sl, tp = price - dist, price + dist * RISK_REWARD
        else:
            sl, tp = price + dist, price - dist * RISK_REWARD

    return {
        "state": state, "price": price, "entry": entry, "sl": sl, "tp": tp,
        "conds": chosen["conds"], "passed": chosen["passed"], "total": chosen["total"],
        "indicators": {"ma21": ma21, "ma50": ma50, "ma200": ma200,
                       "rsi": rsi5[-1] if rsi5 else None, "atr": atr5, "in_session": in_session},
    }


# ============================= TELEGRAM =============================
def send_telegram(text):
    if not TELEGRAM_TOKEN or not TELEGRAM_CHAT_ID:
        print("Telegram not configured, skipping send. Message would have been:\n", text)
        return
    url = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage"
    try:
        r = requests.post(url, json={"chat_id": TELEGRAM_CHAT_ID, "text": text, "parse_mode": "HTML"}, timeout=15)
        if not r.ok:
            print("Telegram send failed:", r.status_code, r.text)
    except Exception as e:
        print("Telegram send error:", e)


def fmt(n, d=2):
    return "—" if n is None else f"{n:.{d}f}"


def build_message(res):
    state = res["state"]
    lines = []
    if state == "BUY":
        lines.append("🟢 <b>XAU BUY SIGNAL</b>")
    elif state == "SELL":
        lines.append("🔴 <b>XAU SELL SIGNAL</b>")
    elif state == "PRE_BUY":
        lines.append("🟡 <b>Pre-signal: BUY building</b>")
    elif state == "PRE_SELL":
        lines.append("🟡 <b>Pre-signal: SELL building</b>")

    lines.append(f"Price: ${fmt(res['price'])}")
    if res.get("entry") is not None:
        lines.append(f"Entry: ${fmt(res['entry'])} | SL: ${fmt(res['sl'])} | TP: ${fmt(res['tp'])}")
    lines.append(f"Conditions met: {res['passed']}/{res['total']}")
    lines.append("")
    for _, label, passed in res["conds"]:
        lines.append(f"{'✅' if passed else '▫️'} {label}")
    return "\n".join(lines)


# ============================= STATE PERSISTENCE =============================
def load_state():
    try:
        with open(STATE_FILE) as f:
            return json.load(f)
    except Exception:
        return {"last_state": "NONE"}


def save_state(state):
    with open(STATE_FILE, "w") as f:
        json.dump(state, f, indent=2)


# ============================= MAIN =============================
def main():
    now_utc = datetime.now(timezone.utc)
    is_manual_run = os.environ.get("GITHUB_EVENT_NAME") == "workflow_dispatch"

    if not in_session_window(now_utc) and not is_manual_run:
        print("Outside trading session window (PKT). Skipping this run.")
        return

    try:
        points = fetch_intraday()
        spot = fetch_spot()
    except Exception as e:
        print("Data fetch failed:", e)
        sys.exit(0)  # don't fail the workflow on a transient API hiccup

    candles5 = build_candles(points, 5)
    candles15 = build_candles(points, 15)
    candles30 = build_candles(points, 30)
    candles60 = build_candles(points, 60)

    res = evaluate(candles5, candles15, candles30, candles60, now_utc, bypass_session=is_manual_run)
    print("Evaluated state:", res.get("state"), "| spot:", spot.get("spot_usd_oz"))

    if res.get("state") == "WARMING_UP":
        if is_manual_run:
            send_telegram("⏳ Demo run: still building candle history from live ticks — "
                           "try again in a few minutes once more data has accumulated.")
        print("Still warming up, not enough candle history yet.")
        return

    state_store = load_state()
    last_state = state_store.get("last_state", "NONE")
    current_state = res.get("state")

    if is_manual_run:
        # Manual/demo run: always send a status message so you can confirm Telegram delivery,
        # regardless of whether the state actually changed.
        prefix = "🧪 <b>Demo run</b>\n\n" if current_state == "NO_TRADE" else ""
        send_telegram(prefix + build_message(res) if current_state != "NO_TRADE" else
                      prefix + f"Price: ${fmt(res['price'])}\nConditions met: {res['passed']}/{res['total']}\n\n" +
                      "\n".join(f"{'✅' if p else '▫️'} {label}" for _, label, p in res["conds"]))
        print("Manual run: notification sent regardless of state change.")
        return

    if current_state in ("BUY", "SELL", "PRE_BUY", "PRE_SELL") and current_state != last_state:
        send_telegram(build_message(res))
        state_store["last_state"] = current_state
        state_store["last_signal_time"] = now_utc.isoformat()
        save_state(state_store)
    elif current_state == "NO_TRADE" and last_state != "NONE":
        state_store["last_state"] = "NONE"
        save_state(state_store)
    else:
        print("No state change, no notification sent.")


if __name__ == "__main__":
    main()
