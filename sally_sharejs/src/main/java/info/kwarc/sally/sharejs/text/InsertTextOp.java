package info.kwarc.sally.sharejs.text;

import java.io.IOException;

import com.fasterxml.jackson.annotation.JsonIgnore;
import com.fasterxml.jackson.core.JsonGenerator;
import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.databind.JsonSerializable;
import com.fasterxml.jackson.databind.SerializerProvider;
import com.fasterxml.jackson.databind.jsontype.TypeSerializer;

public class InsertTextOp implements IBasicTextOp, JsonSerializable{
	@JsonIgnore
	String text;
	
	public InsertTextOp(String text) {
		this.text = text;
	}

	public String getText() {
		return text;
	}
	
	public void setText(String text) {
		this.text = text;
	}

	@Override
	public void serialize(JsonGenerator arg0, SerializerProvider arg1)
			throws IOException, JsonProcessingException {
		arg0.writeString(text);
	}

	@Override
	public void serializeWithType(JsonGenerator arg0, SerializerProvider arg1,
			TypeSerializer arg2) throws IOException, JsonProcessingException {
		arg0.writeString(text);
	}
}
