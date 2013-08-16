<link rel="stylesheet" type="text/css" href="/pricing/pricing.css" />
<link rel="stylesheet" type="text/css" href="/sally/jobad/build/release/JOBAD.css" />

<script src="/sally/jquery/jquery-1.7.2.js"></script>
<script src="/sally/jobad/build/release/JOBAD.js"></script>

<script>
$(function() {
	$(".result-row").each(function(o, obj) {
		$(obj).click(function() {
			$.get("/sally/instance/navigate", {uri:$(obj).attr("id"), file:$(obj).attr("file")}, function() {
			});			
		});
	});
});
</script>

Instances for URI ${node}

<table>
<#list solutions as solution>
<tr  class="result-row" id="${solution.get("cadlabel")}" file="${solution.get("file")}">
<td>${solution.get("cadlabel")}</td> 
</tr>
</#list>
</table>