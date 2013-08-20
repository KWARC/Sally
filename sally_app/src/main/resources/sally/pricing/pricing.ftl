<link rel="stylesheet" type="text/css" href="/pricing/pricing.css" />
<link rel="stylesheet" type="text/css" href="/sally/jobad/build/release/JOBAD.css" />

<link rel="stylesheet" type="text/css" href="/sally/tablesorter/blue/style.css" />

<script src="/sally/jquery/jquery-1.7.2.js"></script>
<script src="/sally/jobad/build/release/JOBAD.js"></script>
<script src="/sally/tablesorter/jquery.tablesorter.min.js"></script>

<script>
$(function() {

	$("#tbl").tablesorter( { sortList: [[0,0]] } );
	$(".result-row").each(function(o, obj) {
		$(obj).click(function() {
			$.get("/sally/pricing/navigate", {uri:$(obj).attr("id")}, function() {
			});			
		});
	});
});
</script>

<h2>Pricing for CAD Node ${node}</h2>

<span class="explanation">Select the spreadsheet item you want to navigate to</span>

<table id="tbl" class="tablesorter">
<thead>
<tr>
	<th>Vendor</th>
	<th>Thread</th>
	<th>Head</th>
	<th>Color</th>
	<th>Cost</th>
</tr>
</thead> 
<tbody>
<#list solutions as solution>
<tr  class="result-row" id="${solution.get("fbi")}">
<td>${solution.get("vendorval")!'-'}</td> <td>${solution.get("threadval")!'-'}</td><td>${solution.get("headval")!'-'}</td><td>${solution.get("colorval")!'-'}</td><td>${solution.get("costval")!'-'}</td>
</tr>
</#list>
</tbody>
</table>