`ifndef QUEUE_WRAPPER_VH
`define QUEUE_WRAPPER_VH

class queue_wrapper #(
	int unsigned DATA_WIDTH = 32);

	reg [DATA_WIDTH-1:0] queue[$];

	task push_back(input [DATA_WIDTH-1:0] data);
		queue.push_back(data);
	endtask

	task push_front(input [DATA_WIDTH-1:0] data);
		queue.push_front(data);
	endtask

	function [DATA_WIDTH-1:0] pop_front();
		pop_front = queue.pop_front();
	endfunction

	task print_queue();
		integer i;
		$display("Queue contains: ");

		for (i = 0; i < queue.size(); i++) begin
			$display("%h", queue[i]);
	end
	endtask

	function integer size();
		size = queue.size();
	endfunction

	function [DATA_WIDTH-1:0] get(integer i);
		get = queue[i];
	endfunction

	// Unpack the fifo, but reverse the bytes for every fifo entry
	// This is used when the fifo stores data in the opposite bit direction ([0:MAX-1])
	task unpack_8b_rev(queue_wrapper#(8) data_unpacked);
		integer queue_i, arr_i, i;
		integer queue_size;
		integer unpacked_arr_size;
		integer bytes_per_word;

		bytes_per_word = (DATA_WIDTH / 8);
		queue_size = queue.size();
		unpacked_arr_size = queue_size * bytes_per_word;

		for(queue_i = 0, arr_i = 0; queue_i < queue_size; queue_i = queue_i + 1)
			for(i = 0; i < bytes_per_word; i = i + 1, arr_i = arr_i + 1)
				data_unpacked.push_back(queue[queue_i][DATA_WIDTH - (i + 1)*8 +: 8]);
	endtask

	task fill_from_file();
		input string fn;

		integer fd;
		reg [DATA_WIDTH-1:0] data;

		fd = $fopen(fn, "r");
		if (!fd) begin
			$display("Oops! %s not found!", fn);
			$finish;
		end

		while (!$feof(fd)) begin
			$fscanf(fd, "%h\n", data);
			queue.push_back(data);
		end
		$fclose(fd);
	endtask

	task compare;
		input queue_wrapper#(DATA_WIDTH) cmp_queue;

		integer i;

		for (i = 0; i < cmp_queue.size(); i=i+1) begin
			if (queue[i] !== cmp_queue.get(i))
				$display("Word no. %d from block no %d does not match!", i, i / 4);
		end
	endtask

endclass

`endif
