module top;

localparam NUM_REQUESTERS = 4;

logic [NUM_REQUESTERS-1:0] reqs_i, grants_o;

logic clk_i, reset_i, yumi_i;

// bsg_arb_round_robin #(NUM_REQUESTERS) arbiter(.clk_i(clk_i), .reset_i(reset_i), .reqs_i(reqs_i), .grants_o(grants_o), .yumi_i(yumi_i));
bsg_arb_round_robin arbiter(.clk_i(clk_i), .reset_i(reset_i), .reqs_i(reqs_i), .grants_o(grants_o), .yumi_i(yumi_i));

bit [$clog2(NUM_REQUESTERS)-1:0] agent_1, agent_2;

bit agent_2_should_be_granted;

assign yumi_i = 1'b1;

default clocking CLK @(posedge clk_i);
endclocking

assume_stable_valid_agent_1: assume property (disable iff (reset_i) $stable(agent_1) && (agent_1 < NUM_REQUESTERS));
assume_stable_valid_agent_2: assume property (disable iff (reset_i) $stable(agent_2) && (agent_2 < NUM_REQUESTERS) && (agent_1 != agent_2));

// Set agent_2_should_be_granted if there is an outstanding request on agent 2, i.e. agent_2 has to be granted,
// and it cannot be granted in this cycle since some other agent is granted in this cycle.

always_ff @(posedge clk_i or posedge reset_i)
    if (reset_i)                     agent_2_should_be_granted <= 0;
    else
      if (grants_o[agent_2])       agent_2_should_be_granted <= 0;
      else if (reqs_i[agent_1] && grants_o[agent_1] && reqs_i[agent_2])
                                   agent_2_should_be_granted <= 1;

// Round robin arbiter has a round that lasts NUM_REQUESTERS cycles and within that round, if any outstanding request is there, it should be granted.
assert_fairness: assert property (disable iff (reset_i) $rose(agent_2_should_be_granted) |-> ##[1:NUM_REQUESTERS] $fell(agent_2_should_be_granted));

// Within a round, ensure that every request is granted, irrespective of other requests
assert_safety: assert property (disable iff (reset_i) $rose(reqs_i[agent_1]) |-> ##[1:NUM_REQUESTERS] $rose(grants_o[agent_1]));

// No spurious grants
assert_no_grant_without_request: assert property (disable iff (reset_i) (!reqs_i[agent_1]) |=> !grants_o[agent_1]);

// No spurious grants, stronger form
assert_no_grant_without_request_strong: assert property (disable iff (reset_i) (!reqs_i[agent_1][*NUM_REQUESTERS]) |=> !grants_o[agent_1]);

// One and only one grant for a non-zero request
assert_only_one_grant_for_non_zero_request: assert property (disable iff (reset_i) reqs_i |=> $onehot(grants_o));

// cover all requests low
cover property (!reqs_i);

// cover all requests high
cover property ($countones(reqs_i) == NUM_REQUESTERS);

// cover precondition of fairness check
cover property (agent_2_should_be_granted);

endmodule
