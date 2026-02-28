# Formal Verification of Round Robin Arbiter

## Notes:
- Design file taken from https://github.com/bespoke-silicon-group/basejump_stl
- As there is an issue in HW-CBMC with parsing the design module, I used Yosys Slang to parse and then write to SystemVerilog file. This synthesized SystemVerilog file is then loaded into HW-CBMC and properties are proven on it.
  
## Properties
- Fairness property on the the fairness of the Round Robin algorithm. This proves that there is no starvation for any requester.
- Safety property that every request is granted within a round. A round is defined as a window of cycles equal to the number of requesters. Within a round, every requester has to be granted.
- There should be no grant without its corresponding request.
- Not more than 1 grant at any given time.
- Cover properties to cover no requests and all requests high, to ensure our Formal environment does not prevent such behaviours from occuring.

## Run Command
`ebmc --top top top.sv bsg_arb_round_robin_yosys.sv`

## Results
```
[top.assume_stable_valid_agent_1] always (disable iff (top.reset_i) $stable(top.agent_1) && top.agent_1 < top.NUM_REQUESTERS): ASSUMED
[top.assume_stable_valid_agent_2] always (disable iff (top.reset_i) $stable(top.agent_2) && top.agent_2 < top.NUM_REQUESTERS && top.agent_1 != top.agent_2): ASSUMED
[top.assert_fairness] always (disable iff (top.reset_i) $rose(top.agent_2_should_be_granted) |-> (##[1:top.NUM_REQUESTERS] $fell(top.agent_2_should_be_granted))): PROVED up to bound 5
[top.assert_safety] always (disable iff (top.reset_i) $rose(top.reqs_i[top.agent_1]) |-> (##[1:top.NUM_REQUESTERS] $rose(top.grants_o[top.agent_1]))): PROVED up to bound 5
[top.assert_no_grant_without_request] always (disable iff (top.reset_i) !top.reqs_i[top.agent_1] |=> !top.grants_o[top.agent_1]): PROVED up to bound 5
[top.assert_no_grant_without_request_strong] always (disable iff (top.reset_i) (!top.reqs_i[top.agent_1] [*top.NUM_REQUESTERS]) |=> !top.grants_o[top.agent_1]): PROVED up to bound 5
[top.assert_only_one_grant_for_non_zero_request] always (disable iff (top.reset_i) top.reqs_i |=> $onehot(top.grants_o)): PROVED up to bound 5
[top.cover.1] cover !top.reqs_i: PROVED
[top.cover.2] cover $countones(top.reqs_i) == top.NUM_REQUESTERS: PROVED
[top.cover.3] cover top.agent_2_should_be_granted: PROVED
```
