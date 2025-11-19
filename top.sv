module top;

logic [15:0] reqs_i, grants_o;
logic clk_i, reset_i, yumi_i;

bsg_arb_round_robin #(16) arbiter(.clk_i(clk_i), .reset_i(reset_i), .reqs_i(reqs_i), .grants_o(grants_o), .yumi_i(yumi_i));

bit [3:0] agent_1, agent_2;

assume_stable_agent_1: assume property (@(posedge clk_i) disable iff (reset_i) $stable(agent_1));
assume_stable_agent_2: assume property (@(posedge clk_i) disable iff (reset_i) $stable(agent_2));

bit agent_2_should_be_granted;

always_ff @(posedge clk or posedge reset)
    if (reset)                     agent_2_should_be_granted <= 0;
    else
      if (grants_o[agent_2])       agent_2_should_be_granted <= 0;
      else if (reqs_i[agent_1] && grants_o[agent_1] && reqs_i[agent_2])
                                   agent_2_should_be_granted <= 1;


assert_fairness: assert property (@(posedge clk_i) disable iff (reset_i) grants_o[agent_2] |=> !agent_1_should_be_granted);
assert_safety: assert property (@(posedge clk_i) disable iff (reset_i) reqs_i[agent_1] |-> s_eventually grants_o[agent_1]);

endmodule
