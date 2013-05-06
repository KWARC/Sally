Token=${token}
Editing ${Sheet}!${StartRow}:${StartCol}-${EndRow}:${EndCol}

<form method="POST">
	<label>Name</label><input type="textfield"/> <br/>
	<label>Ontology</label><input type="textfield"/> <input type="submit" value="Browse" name="action"> <br/>
	<input type="hidden" name="s" value="${token}"> 	
	<input type="submit" name="action" value="Save">
</form>