class queue_wrapper #(
	int unsigned DATA_WIDTH = 32);

	static reg [DATA_WIDTH-1:0] queue[$];

	static task push_back(input [DATA_WIDTH-1:0] data);
		queue.push_back(data);
	endtask

	static task push_front(input [DATA_WIDTH-1:0] data);
		queue.push_front(data);
	endtask

	static function [DATA_WIDTH-1:0] pop_front();
		pop_front = queue.pop_front();
	endfunction

	static task print_queue();
		integer i;
		$display("Queue contains: ");
		for (i = 0; i < queue.size(); i++) begin
			$display(" %h", queue[i]);
	end
	endtask

	static function integer size();
		size = queue.size();
	endfunction

endclass

