<link rel="stylesheet" type="text/css" href="/pricing/pricing.css" />
<link rel="stylesheet" type="text/css" href="/sally/jobad/build/release/JOBAD.css" />

<script src="/sally/jquery/jquery-1.7.2.js"></script>
<script src="/sally/jobad/build/release/JOBAD.js"></script>

<script>
$(function() {
	$(".result-row").each(function(o, obj) {
		$(obj).click(function() {
			console.log(obj);
		});
	});
});
</script>

<table>
<#list solutions as solution>
<tr  class="result-row">
<td>${solution.get("vendorval")}</td> <td>${solution.get("threadval")}</td><td>${solution.get("colorval")}</td><td>${solution.get("costval")}</td>
</tr>
</#list>
</table>