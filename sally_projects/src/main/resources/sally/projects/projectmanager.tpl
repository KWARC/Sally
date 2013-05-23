<h1>Project Manager</h1>

<form method="POST">
Project root <input type="text" name="root" value="${root}"> <br/>
<table>
<th>Index id</th>
<th>Enabled</th>
<th>Operations</th>
<tr>
<#list indexes as index>
<td>
	<label for="${index}">${index}</label> <br>
</td>
<td>
<input type="checkbox" id="${index}">
</td>
</#list>
<td>
	<button>restart</button>
	<button>logs</button>
</td>
</tr>
</table>

<input type="submit" value="Update">

</form>
