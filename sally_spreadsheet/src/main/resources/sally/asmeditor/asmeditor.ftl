${Sheet}!${StartRow}:${StartCol}-${EndRow}:${EndCol}

<form method="POST">
	<label>Type? </label>
	
	<input type="radio" checked name="rangeType" id="label_label"/><label for="label_label">Label</label>
	<input type="radio" name="rangeType" id="fb_label"/><label for="fb_label">Functional Block</label> <br/>

	<label>Ontology</label>
	<input type="textfield" name="IM" value="https://tnt.kwarc.info/repos/stc/fcad/flange/cds/isohexnut.omdoc?isohexnut?isohexnut" size="80" /> <br/>
	
	<input type="hidden" name="pid" value="${token}">
	<input type="submit" name="action" value="Save">
</form>