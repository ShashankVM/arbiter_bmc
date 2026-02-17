module top;

localparam NUM_REQUESTERS = 4;

logic [NUM_REQUESTERS-1:0] reqs_i, grants_o;

logic clk_i, reset_i, yumi_i;

bsg_arb_round_robin #(NUM_REQUESTERS) arbiter(.clk_i(clk_i), .reset_i(reset_i), .reqs_i(reqs_i), .grants_o(grants_o), .yumi_i(yumi_i));

bit [$clog2(NUM_REQUESTERS)-1:0] agent_1, agent_2;

bit agent_2_should_be_granted;

assign yumi_i = 1'b1;

default clocking CLK @(posedge clk_i);
endclocking

assume_stable_valid_agent_1: assume property (disable iff (reset_i) $stable(agent_1) && (agent_1 < NUM_REQUESTERS));
assume_stable_valid_agent_2: assume property (disable iff (reset_i) $stable(agent_2) && (agent_2 < NUM_REQUESTERS));



always_ff @(posedge clk_i or posedge reset_i)
    if (reset_i)                     agent_2_should_be_granted <= 0;
    else
      if (grants_o[agent_2])       agent_2_should_be_granted <= 0;
      else if (reqs_i[agent_1] && grants_o[agent_1] && reqs_i[agent_2])
                                   agent_2_should_be_granted <= 1;


assert_fairness: assert property (disable iff (reset_i) grants_o[agent_2] |=> !agent_2_should_be_granted);
assert_safety: assert property (disable iff (reset_i) reqs_i[agent_1] |-> s_eventually grants_o[agent_1]);
assert_no_grant_without_request: assert property (disable iff (reset_i) (!reqs_i[agent_1]) |=> !grants_o[agent_1]);
assert_only_one_grant_for_non_zero_request: assert property (disable iff (reset_i) reqs_i |=> $onehot(grants_o));

endmodule
