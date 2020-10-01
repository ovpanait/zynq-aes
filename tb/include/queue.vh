`ifndef QUEUE_WRAPPER_VH
`define QUEUE_WRAPPER_VH

class queue #(
	int unsigned DATA_WIDTH = 32);

	reg [DATA_WIDTH-1:0] q[$];

	task push_back(input [DATA_WIDTH-1:0] data);
		q.push_back(data);
	endtask

	task push_front(input [DATA_WIDTH-1:0] data);
		q.push_front(data);
	endtask

	function [DATA_WIDTH-1:0] pop_front();
		pop_front = q.pop_front();
	endfunction

	task print_queue();
		integer i;
		$display("Queue contains: ");

		for (i = 0; i < q.size(); i++) begin
			$display("%h", q[i]);
	end
	endtask

	function integer size();
		size = q.size();
	endfunction

	function [DATA_WIDTH-1:0] get(integer i);
		get = q[i];
	endfunction

	task clear;
		q = {};
	endtask

	// Unpack the fifo, but reverse the bytes for every fifo entry
	// This is used when the fifo stores data in the opposite bit direction ([0:MAX-1])
	task unpack_8b_rev(queue#(8) data_unpacked);
		integer queue_i, arr_i, i;
		integer queue_size;
		integer unpacked_arr_size;
		integer bytes_per_word;

		bytes_per_word = (DATA_WIDTH / 8);
		queue_size = q.size();
		unpacked_arr_size = queue_size * bytes_per_word;

		for(queue_i = 0, arr_i = 0; queue_i < queue_size; queue_i = queue_i + 1)
			for(i = 0; i < bytes_per_word; i = i + 1, arr_i = arr_i + 1)
				data_unpacked.push_back(q[queue_i][DATA_WIDTH - (i + 1)*8 +: 8]);
	endtask

	task fill_from_file(input string fn);
		integer fd;
		reg [DATA_WIDTH-1:0] data;

		fd = $fopen(fn, "r");
		if (!fd) begin
			$display("Oops! %s not found!", fn);
			$finish;
		end

		while (!$feof(fd)) begin
			$fscanf(fd, "%h\n", data);
			q.push_back(data);
		end
		$fclose(fd);
	endtask

	function bit compare(input queue#(DATA_WIDTH) cmp_queue);
		integer i;

		compare = 0;
		for (i = 0; i < cmp_queue.size(); i=i+1) begin
			if (q[i] !== cmp_queue.get(i)) begin
				$display("Data at index %d doesn't match!", i);
				$display("Value 1: %H", q[i]);
				$display("Value 2: %H", cmp_queue.get(i));

				compare = 1;
				break;
			end
		end
	endfunction

endclass

`endif
