/* This file was generated by SableCC (http://www.sablecc.org/). */

package src.promela.node;

import src.promela.analysis.*;

@SuppressWarnings("nls")
public final class ABitTypename extends PTypename
{
    private TBit _bit_;

    public ABitTypename()
    {
        // Constructor
    }

    public ABitTypename(
        @SuppressWarnings("hiding") TBit _bit_)
    {
        // Constructor
        setBit(_bit_);

    }

    @Override
    public Object clone()
    {
        return new ABitTypename(
            cloneNode(this._bit_));
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseABitTypename(this);
    }

    public TBit getBit()
    {
        return this._bit_;
    }

    public void setBit(TBit node)
    {
        if(this._bit_ != null)
        {
            this._bit_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._bit_ = node;
    }

    @Override
    public String toString()
    {
        return ""
            + toString(this._bit_);
    }

    @Override
    void removeChild(@SuppressWarnings("unused") Node child)
    {
        // Remove child
        if(this._bit_ == child)
        {
            this._bit_ = null;
            return;
        }

        throw new RuntimeException("Not a child.");
    }

    @Override
    void replaceChild(@SuppressWarnings("unused") Node oldChild, @SuppressWarnings("unused") Node newChild)
    {
        // Replace child
        if(this._bit_ == oldChild)
        {
            setBit((TBit) newChild);
            return;
        }

        throw new RuntimeException("Not a child.");
    }
}
