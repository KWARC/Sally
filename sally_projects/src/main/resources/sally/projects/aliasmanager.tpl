<h1>Alias Manager</h1>
${msg} <br>
Below is the list of currently defined aliases.
 

<form method="POST">
<#list aliases as alias>
	${alias_index + 1}. <input type="text" value="${alias!?split("@")[0]}" size="10" name="keys[]"> <input type="text" value="${alias!?split("@")[1]}" name="values[]"> <br/>
</#list>

New <input type="text" name="keys[]" size="10"> <input type="text" name="values[]"> <br/>
<input type="submit" value="Update">
</form>
