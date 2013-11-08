<script src="/sally/lib/jquery/jquery.min.js"></script>

<script>
	var objids=[<#list ObjectIDs as id >"${id}",</#list>];
	var first = 1;
	var current = 0;
	var last = objids.length;
</script>

Navigating to instance <span id="from"></span> of <span id="to"></span>
<button id="prev">Previous</button>
<button id="next">Next</button>
<script>
	function navigateTo(id) {
		$("#from").text(current+1);
		$.get("navigateTo?id="+id+"&callbackid=${CallbackID}", function() {
		});
	}
	
	$("#next").click(function() {
		current=(current+1)%last;
		navigateTo(objids[current]);
	});

	$("#prev").click(function() {
		current=(current-1+last)%last;
		navigateTo(objids[current]);
	});

	$("#from").text(first);
	$("#to").text(last);
	navigateTo(objids[0]);
</script>