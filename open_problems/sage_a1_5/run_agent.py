"""Drive Sage-A1.5 (llama-server) with a single restricted tool: batch |G,H| computation. No code execution."""
import json, os, sys, time, requests
import sys as _s, os as _o; _s.path.insert(0, _o.path.dirname(_o.path.abspath(__file__)))
from graphs import nonhom, parse, FAMILIES, NAMED
D = os.path.dirname(os.path.abspath(__file__))
URL = "http://127.0.0.1:8088/v1/chat/completions"
LOG = open(os.path.join(D, "..", "agent_transcript.md"), "a")
def log(s): LOG.write(s + "\n"); LOG.flush()

TOOLS = [{"type": "function", "function": {
    "name": "nonhom_batch",
    "description": "Compute |G,H| exactly (min number of edges of G to delete so that a homomorphism G->H exists) for up to 40 (G,H) pairs. "
        "Graph spec strings: named graphs " + ", ".join(sorted(NAMED)) + "; families with integer args: " +
        "; ".join(sorted(FAMILIES)) + " (e.g. 'cycle 7', 'kneser 6 2', 'circulant 13 1 5', 'gen_petersen 7 2', 'power_cycle 11 2', "
        "'complete_multipartite 2 3 4', 'mycielski 4' = Grotzsch, 'random_regular 3 20 SEED', 'gnp N P_PERCENT SEED', 'wheel n' = hub + C_{n-1}); "
        "shorthands K5, C7, P4, W6, Q3, K3,3; explicit 'edges 0-1 1-2 2-0'; operators 'line X', 'complement X', 'mycielskian X'. Max 64 vertices. "
        "exact=false means the 60 s timeout hit and value is only an upper bound. Note |G,K_k|=0 iff chi(G)<=k.",
    "parameters": {"type": "object", "properties": {"pairs": {"type": "array", "items": {"type": "array", "items": {"type": "string"}, "minItems": 2, "maxItems": 2}}},
                   "required": ["pairs"]}}}]

DONE = {(g, h): v for g, h, m, v in json.load(open(os.path.join(D, "seed_data.json")))}
def call_tool(args):
    out = []; dup = 0
    for p in args.get("pairs", [])[:40]:
        if tuple(p) in DONE: dup += 1; continue
        try:
            r = nonhom(p[0], p[1]); out.append(r)
            if r.get("exact"): DONE[tuple(p)] = r["value"]
        except Exception as e: out.append({"G": p[0], "H": p[1], "error": str(e)})
    if dup: out.append({"note": f"{dup} pair(s) skipped: already computed earlier (see previous results). Do not repeat pairs; test NEW graphs or targets."})
    return json.dumps(out)

msgs = [{"role": "system", "content": open(os.path.join(D, "system.md")).read()},
        {"role": "user", "content": open(os.path.join(D, "task.md")).read()}]
MAX_TURNS = int(sys.argv[1]) if len(sys.argv) > 1 else 40
tool_calls_total = 0
for turn in range(MAX_TURNS):
    t = time.time()
    r = requests.post(URL, json={"messages": msgs, "tools": TOOLS, "temperature": 0.6, "top_p": 0.95, "max_tokens": 4000, "chat_template_kwargs": {"enable_thinking": False}}, timeout=10800).json()
    if "choices" not in r: log(f"\n**server error:** {r}"); break
    m = r["choices"][0]["message"]; u = r.get("usage", {})
    log(f"\n## Turn {turn}  ({time.time()-t:.0f}s, prompt={u.get('prompt_tokens')}, gen={u.get('completion_tokens')})")
    if m.get("reasoning_content"): log("<details><summary>reasoning</summary>\n\n" + m["reasoning_content"] + "\n</details>\n")
    if m.get("content"): log("**Sage:** " + m["content"])
    msgs.append({k: v for k, v in m.items() if k in ("role", "content", "tool_calls")})
    calls = m.get("tool_calls") or []
    if not calls:
        if "FINAL REPORT" in (m.get("content") or ""): break
        if turn >= MAX_TURNS - 2 or tool_calls_total >= 10:
            msgs.append({"role": "user", "content": "Time is up. Write your answer now, beginning with 'FINAL REPORT'."})
        else:
            msgs.append({"role": "user", "content": "Continue the research with the tool. When completely done, write your answer beginning with 'FINAL REPORT'."})
        continue
    for c in calls:
        tool_calls_total += 1
        try: args = json.loads(c["function"]["arguments"])
        except Exception as e: args = {}; 
        log("**tool call:** `" + json.dumps(args)[:3000] + "`")
        res = call_tool(args)
        log("**result:** `" + res[:6000] + "`")
        msgs.append({"role": "tool", "tool_call_id": c.get("id", ""), "content": res})
    if tool_calls_total >= 12:
        msgs.append({"role": "user", "content": "Tool budget exhausted. Write your answer now, beginning with 'FINAL REPORT'."})
json.dump(msgs, open(os.path.join(D, "..", "agent_messages.json"), "w"), indent=1)
log("\n--- done ---")
