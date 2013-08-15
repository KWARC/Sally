<link rel="stylesheet" type="text/css" href="/pricing/pricing.css" />
<link rel="stylesheet" type="text/css" href="/sally/jobad/build/release/JOBAD.css" />

<script>
	
</script>
<script src="/sally/jquery/jquery-1.7.2.js"></script>
<script src="/sally/jobad/build/release/JOBAD.js"></script>

<script>
$(function() {
	$(".result-row").each(function(o, obj) {
		$(obj).click(function() {
			$.get("/sally/pricing/navigate", {uri:$(obj).attr("id")}, function() {
				console.log("ok");
			});			
		});
	});
});
</script>

<table>
<#list solutions as solution>
<tr  class="result-row" id="${solution.get("fbi")}">
<td>${solution.get("vendorval")}</td> <td>${solution.get("threadval")}</td><td>${solution.get("colorval")}</td><td>${solution.get("costval")}</td>
</tr>
</#list>
</table>